-- Prove2me | Theorems.Thm_PrettyGoodCriterion_corollary_18
-- name    : PrettyGoodCriterion.corollary_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:39:19.945716+00:00
-- url     : https://prove2.me/theorems/964b01e3-39ed-4a72-acd9-01ecd1684326
-- title:
--   Corollary 18 — constant successful block decoding: $\Pr[\hat c=c]\ge 1-p_e(\sigma_0,\sigma_1)/\delta$
-- statement:
--   Let $b\mapsto\sigma_b$ be a binary-input output-symmetric cq channel with density outputs $\sigma_0,\sigma_1$ and let $\delta>0$. For every $n$ and every code $\mathcal C\subseteq\{0,1\}^n$ with $|\mathcal C|\ge2$ and $d_{\min}(\mathcal C)\ge\delta n$, the PGM of $\mathcal C$ applied to $\sigma_c$, $c$ uniform, decodes correctly with probability
--   $$\Pr[\hat c=c]\ge1-\frac{p_e(\sigma_0,\sigma_1)}{\delta}.$$
--   In particular, if $p_e(\sigma_0,\sigma_1)<\delta$, then $\Pr[\hat c=c]\ge\Omega(1)$: there is a constant $\kappa>0$, depending only on the channel and $\delta$, with $\Pr[\hat c=c]\ge\kappa$ for every such $n$ and $\mathcal C$.
--
--   This is the only step of the main proof that uses the minimum distance of the code.
--
--   Differences from the source:
--   - reading: Pr[ĉ = c] ⩾ Ω(1) → ∃ κ > 0, chosen after σ and δ and before n and 𝒞, with κ ≤ Pr[ĉ = c] for every n and every code with |𝒞| ⩾ 2 and d_min(𝒞) ⩾ δn; reason: Ω(1) means a positive lower bound independent of n and 𝒞
--   - encoding: d_min(𝒞) ⩾ δn → BeatingGV42.MinDistAtLeast 𝒞 (δ * n): distinct codewords are at Hamming distance ⩾ δn; reason: equivalent for |𝒞| ⩾ 2
--   - encoding: the PGM of 𝒞, i.e. of the uniform ensemble {(|𝒞|⁻¹, σ_c) : c ∈ 𝒞} with outcomes ĉ ∈ 𝒞 → the PGM (Definition 2.7) of the ensemble indexed by the subtype {c // c ∈ 𝒞} with prior |𝒞|⁻¹ and states HolevoCQ.wordState σ n c; reason: the same ensemble; the outcome set is the code itself
--   - encoding: ℂ^d, d × d matrices → matrices indexed by an arbitrary finite type ι; reason: ℂ^d is the case ι = Fin d, and every finite type is Fin d up to relabelling, which changes no trace, product or positivity
--   - encoding: probabilities Tr(σ_x M_x̂) (and the other traces of products of positive semidefinite matrices) → real parts of the traces; reason: these traces are real; taking the real part changes no value
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), Corollary 18, p.22 (PDF 24)

import Mathlib
import Definitions.Def_PrettyGoodCriterion_rateFunction
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_PrettyGoodCriterion_pgmError
import Definitions.Def_PrettyGoodCriterion_OutputSymmetric
import Definitions.Def_PrettyGoodCriterion_codePGM

open scoped ComplexOrder

namespace PrettyGoodCriterion

/-- **Corollary 18 (Constant successful block decoding)**, Alrabiah–Guruswami,
arXiv:2608.09347 (held version), p.22 (PDF 24).

Under the hypotheses of Theorem 17, if moreover `d_min(𝒞) ⩾ δn` for some `δ > 0`, then
`Pr[ĉ = c] ⩾ 1 − p_e(σ₀, σ₁)/δ`. In particular, if `p_e(σ₀, σ₁) < δ` then `Pr[ĉ = c] ⩾ Ω(1)`.

**Formalization Note.** `Ω(1)` is read as a positive constant `κ`, chosen after `σ` and `δ` and
before `n` and `𝒞`, that lower-bounds `Pr[ĉ = c]` for every `n` and every code `𝒞` with
`|𝒞| ⩾ 2` and `d_min(𝒞) ⩾ δn`. -/
theorem corollary_18 {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Fin 2 → Matrix ι ι ℂ)
    (hσ : ∀ b, QAlgorithms.IsDensityMatrix (σ b)) (hsym : OutputSymmetric σ) (δ : ℝ) (hδ : 0 < δ) :
    (∀ (n : ℕ) (C : Finset (Fin n → Fin 2)), 2 ≤ C.card → BeatingGV42.MinDistAtLeast C (δ * n) →
        1 - pgmBitErrorUniform σ / δ ≤ pgmBlockSuccess σ C) ∧
      (pgmBitErrorUniform σ < δ → ∃ κ : ℝ, 0 < κ ∧
        ∀ (n : ℕ) (C : Finset (Fin n → Fin 2)), 2 ≤ C.card → BeatingGV42.MinDistAtLeast C (δ * n) →
          κ ≤ pgmBlockSuccess σ C) := by sorry

end PrettyGoodCriterion
