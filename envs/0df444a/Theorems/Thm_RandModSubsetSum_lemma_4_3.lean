-- Prove2me | Theorems.Thm_RandModSubsetSum_lemma_4_3
-- name    : RandModSubsetSum.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:18.880189+00:00
-- url     : https://prove2.me/theorems/cc27c9e4-e033-4108-ba0e-ff25dc3d9a16
-- title:
--   Lemma 4.3 — entropy conditions give $\mathrm{Var}(Z)/\mathbb E(Z)^2\le\mathrm{poly}(n)2^{-n(\gamma-\eta)}$
-- statement:
--   Fix positive stratum weights $w$ with $\sum_rw_r=1$, nominal kernels $R^{(r)}_j$ satisfying the conditions of §3.1, rates $K_1>\dots>K_7>0$ ($K_8=0$), $\gamma>0$, and a constant $C_0$. Let $x$ be a root nearly balanced in every stratum, $\rho_r=h_r/n_r$, and let $p_1,\dots,p_7$ be distinct primes with $|\log_2p_i-(K_i-K_{i+1})n|\le C_0$. Suppose that at $\rho$
--
--   $$E_{a,b}\ge aK_1+bK_2+\gamma\ \text{for the five profiles},\qquad D_j\ge K_{j+1}+\gamma\ (2\le j<7).$$
--
--   Let $Z$ count the representations of $x$ with the prescribed exact types of §6.2 that match all residue labels in the auxiliary residue model. Then, for every $\varepsilon>0$ there are $C,e,N$ such that for all $n\ge N$
--
--   $$\frac{\mathrm{Var}(Z)}{\mathbb E(Z)^2}\le C(n+1)^e\,2^{-(\gamma-\varepsilon)n}\qquad\text{and}\qquad\Pr(Z=0)\le C(n+1)^e\,2^{-(\gamma-\varepsilon)n},$$
--
--   uniformly over the nearly balanced roots and the primes.
--
--   This is the correctness core of the method: the entropy inequalities, checked for the paper's parameters in (41), guarantee that some representation of the root survives all residue constraints.
--
--   **Formalization Note** The paper's $\eta$ is the rounding loss of Appendix A; it tends to $0$ with $n$ and is below $10^{-12}$ for large $n$ (54). The profile conditions are stated for every nonzero observation space $S=\mathrm{row}(B)\le\mathbb F_7^3$, which is equivalent to the conditions on the minima $E_{a,b}$.
--
--   Differences from the source:
--   - reading: Var(Z)/E(Z)² ≤ poly(n) 2^{−n(γ−η)}, η the uniform rounding loss of Appendix A → ∀ ε > 0 ∃ C e N, ∀ n ≥ N: Var(Z)/E(Z)² ≤ C (n+1)^e 2^{−(γ−ε)n}; reason: η → 0 with n (δ_i^{(r)} ≤ 226/n_r in (50)); the ∀ε form implies the bound for the constant η of (54) and is the stronger reading
--   - encoding: Pr(Z = 0) ≤ 2^{−Ω(n)} whenever γ > η → Pr(Z = 0) ≤ C (n+1)^e 2^{−(γ−ε)n}; reason: explicit form of 2^{−Ω(n)} for every ε < γ
--   - generalization: positive rational weights and rational kernels → positive real weights and real kernels; reason: the proof does not use rationality; the paper's parameters are a special case
--   - encoding: E_{a,b} ≥ aK₁ + bK₂ + γ for the five profiles (minimum over B) → the inequality for every nonzero S = row(B) ≤ F₇³ with (a, b) = (b₁(S), b₂(S)); reason: a minimum is ≥ a bound iff every term is
--   - encoding: log₂ p_i = (K_i − K_{i+1})n + O(1) → |log₂ p_i − (K_i − K_{i+1})n| ≤ C₀ for a fixed C₀; reason: pins the O(1); C, e, N may depend on C₀
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), Lemma 4.3, p. 22; (9), p. 22; Appendix A, pp. 55–57

import Mathlib
import Definitions.Def_RandModSubsetSum_Strata
import Definitions.Def_RandModSubsetSum_Template
import Definitions.Def_RandModSubsetSum_Kernels

open scoped BigOperators

namespace RandModSubsetSum

/-- **Lemma 4.3** (entropy conditions imply the second-moment bound). Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), Lemma 4.3, p. 22, with
(9), p. 22, and Appendix A, pp. 55–57.

Fix positive stratum weights `w` summing to one, nominal kernels `R` satisfying the conditions of
§3.1, rates `K_1 > ⋯ > K_7 > 0` (`K_8 = 0`),
`γ > 0` and a constant `C₀`. Suppose the primes satisfy `|log₂ p_i − (K_i − K_{i+1}) n| ≤ C₀`, and,
at `ρ_r = h_r/n_r` of the nearly balanced root `x`, that `E_{a,b} ≥ a K_1 + b K_2 + γ` for all five
profiles and `D_j ≥ K_{j+1} + γ` for `2 ≤ j < 7`. Then `Var(Z)/E(Z)² ≤ poly(n) 2^{−n(γ − η)}` and
`Pr(Z = 0) ≤ poly(n) 2^{−n(γ − η)}`, where `Z` counts the prescribed representations (exact types of
§6.2) matching all residue labels, and `η` is the rounding loss of Appendix A.

**Formalization Note.** `η` tends to `0` with `n` (Appendix A, (50): `δ^{(r)}_i ≤ 226/n_r`), so
`poly(n) 2^{−n(γ−η)}` is stated as: for every `ε > 0` there are `C, e, N` with the bound
`C (n+1)^e 2^{−(γ−ε) n}` for all `n ≥ N`, uniformly over the nearly balanced roots and the primes.
The five profile inequalities are stated for every nonzero observation space `S = row(B) ≤ F₇³`,
which is equivalent to the inequality for each minimum `E_{a,b}`. `K i` is `K_{i+1}`. `Pr(Z = 0)`
is the conclusion "in particular" of the lemma (Chebyshev). -/
theorem lemma_4_3 (w : Fin 13 → ℝ) (hw : ∀ r, 0 < w r) (hw1 : ∑ r, w r = 1)
    (R : Kernel) (hR : IsNominalKernel R)
    (K : Fin 7 → ℝ) (hK : StrictAnti K) (hK7 : 0 < K 6) (γ : ℝ) (hγ : 0 < γ) (C₀ : ℝ) :
    ∀ ε > 0, ∃ C : ℝ, ∃ e N : ℕ, ∀ n ≥ N, ∀ x : Fin n → Fin 2, NearBalanced w x →
      ∀ p : Fin 7 → ℕ, Function.Injective p → (∀ i, (p i).Prime) →
      (∀ i, |Real.logb 2 (p i) - (K i - Knext K i) * n| ≤ C₀) →
      (∀ S : ObsSpace, S ≠ ⊥ →
        (b1 S : ℝ) * K 0 + (b2 S : ℝ) * K 1 + γ ≤ obsEntropy w R (rho w x) S) →
      (∀ j : Fin 7, 2 ≤ j.val → K j + γ ≤ Drate w R (rho w x) j.val) →
      varRatio p x (exactFamily w R n x) ≤ C * ((n : ℝ) + 1) ^ e * (2 : ℝ) ^ (-(γ - ε) * n) ∧
      probNoMatch p x (exactFamily w R n x) ≤ C * ((n : ℝ) + 1) ^ e * (2 : ℝ) ^ (-(γ - ε) * n) := by sorry

end RandModSubsetSum
