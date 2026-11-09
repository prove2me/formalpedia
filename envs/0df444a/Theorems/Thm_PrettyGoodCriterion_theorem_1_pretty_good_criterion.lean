-- Prove2me | Theorems.Thm_PrettyGoodCriterion_theorem_1_pretty_good_criterion
-- name    : PrettyGoodCriterion.theorem_1_pretty_good_criterion
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:40:43.306915+00:00
-- url     : https://prove2.me/theorems/3ce34a25-ab03-4edb-85e2-1b5c563bbe78
-- title:
--   Theorem 1 — the pretty good criterion: $p_e(\sigma_0,\sigma_1)<\delta$ implies $R(\mathcal C)\le\chi(\sigma_0,\sigma_1)+O(n^{-1/2})$ and $R_2(\delta)\le\chi(\sigma_0,\sigma_1)$
-- statement:
--   Fix $\delta\in(0,\tfrac12)$ and a finite-dimensional binary-input output-symmetric classical–quantum channel with output density matrices $\sigma_0,\sigma_1$. Suppose its PGM bit error rate is below the relative distance:
--   $$p_e(\sigma_0,\sigma_1)<\delta .$$
--   Then:
--
--   1. there is a constant $K$, depending only on $\delta$ and the channel, such that every binary code $\mathcal C\subseteq\{0,1\}^n$ (any $n$, linear or not, $|\mathcal C|\ge2$) with $d_{\min}(\mathcal C)\ge\delta n$ has rate
--   $$R(\mathcal C)\le\chi(\sigma_0,\sigma_1)+\frac{K}{\sqrt n};\qquad(2)$$
--   2. maximizing over all such codes and letting $n\to\infty$,
--   $$R_2(\delta)\le\chi(\sigma_0,\sigma_1).\qquad(3)$$
--
--   Every channel with small PGM bit error rate therefore yields an upper bound on the rate of binary codes of relative distance $\delta$. Applied to the binary erasure and binary symmetric channels it gives the Plotkin and Elias–Bassalygo bounds; applied to suitable non-commuting channels it gives both McEliece–Rodemich–Rumsey–Welch bounds and the paper's strict improvements of them.
--
--   **Formalization Note** Density matrices are `QAlgorithms.IsDensityMatrix` (positive semidefinite, trace 1). $O(n^{-1/2})$ is $K/\sqrt n$ with a single $K$ quantified after $\delta,\sigma_0,\sigma_1$ and before $n$ and $\mathcal C$; the bound holds for every $n$, not only eventually. $|\mathcal C|\ge2$ is the paper's standing assumption (p.14) and forces $n\ge1$.
--
--   Differences from the source:
--   - encoding: R(𝒞) ⩽ χ(σ₀, σ₁) + O(n^{−1/2}), the implicit constant depending only on δ and the cq channel → ∃ K, ∀ n 𝒞, … → R(𝒞) ⩽ χ(σ₀, σ₁) + K/√n; reason: the quantifier order the paper states: K after δ, σ₀, σ₁ and before n and 𝒞, for every n
--   - encoding: d_min(𝒞) ⩾ δn → BeatingGV42.MinDistAtLeast 𝒞 (δ * n): distinct codewords are at Hamming distance ⩾ δn; reason: equivalent for |𝒞| ⩾ 2
--   - encoding: R₂(δ) = lim sup (1/n) log A₂(n, ⌈δn⌉) → rateFunction δ, a real Filter.limsup of a sequence in [0, 1], A₂ maximizing over all codes including those with fewer than two words; reason: the sequence is bounded, so the real limsup is the limit superior; codes with one word do not change A₂ once a two-word code exists, and A₂(n, ⌈δn⌉) ⩾ 1 always
--   - encoding: ℂ^d, d × d matrices → matrices indexed by an arbitrary finite type ι; reason: ℂ^d is the case ι = Fin d, and every finite type is Fin d up to relabelling, which changes no trace, product or positivity
--   - encoding: probabilities Tr(σ_x M_x̂) (and the other traces of products of positive semidefinite matrices) → real parts of the traces; reason: these traces are real; taking the real part changes no value
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), Theorem 1, equations (2)–(3), p.2 (PDF 4); proof §3, pp.21–23 (PDF 23–25)

import Mathlib
import Definitions.Def_PrettyGoodCriterion_rateFunction
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_PrettyGoodCriterion_holevoUniform
import Definitions.Def_PrettyGoodCriterion_pgmError
import Definitions.Def_PrettyGoodCriterion_OutputSymmetric

open scoped ComplexOrder

namespace PrettyGoodCriterion

/-- **Theorem 1 (The pretty good criterion)**, Alrabiah–Guruswami, *Binary code rate bounds via
classical–quantum channels*, arXiv:2608.09347 (held version), p.2 (PDF 4); proof §3,
pp.21–23 (PDF 23–25).

Fix `δ ∈ (0, 1/2)` and a finite-dimensional binary-input output-symmetric cq channel with output
density matrices `σ₀, σ₁`. If `p_e(σ₀, σ₁) < δ`, then every binary code `𝒞 ⊆ {0,1}ⁿ` with
`d_min(𝒞) ⩾ δn` satisfies `R(𝒞) ⩽ χ(σ₀, σ₁) + O(n^{−1/2})` (2), the implicit constant depending
only on `δ` and the channel; and `R₂(δ) ⩽ χ(σ₀, σ₁)` (3).

**Formalization Note.** `O(n^{−1/2})` is `K/√n` with one constant `K` chosen after `δ, σ₀, σ₁`
and before `n` and `𝒞`; the bound holds for every `n` and every code with `|𝒞| ⩾ 2` (the paper's
standing assumption, p.14, which forces `n ⩾ 1`). `d_min(𝒞) ⩾ δn` is `BeatingGV42.MinDistAtLeast C (δ * n)`.
`R₂` is the real limit superior `rateFunction` of (1). -/
theorem theorem_1_pretty_good_criterion {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : Fin 2 → Matrix ι ι ℂ) (hσ : ∀ b, QAlgorithms.IsDensityMatrix (σ b)) (hsym : OutputSymmetric σ)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (hpe : pgmBitErrorUniform σ < δ) :
    (∃ K : ℝ, ∀ (n : ℕ) (C : Finset (Fin n → Fin 2)), 2 ≤ C.card →
        BeatingGV42.MinDistAtLeast C (δ * n) → rate C ≤ holevoUniform σ + K / Real.sqrt n) ∧
      rateFunction δ ≤ holevoUniform σ := by sorry

end PrettyGoodCriterion
