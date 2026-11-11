-- Prove2me | Theorems.Thm_SparseTensorInj_Certify_lemma_42
-- name    : SparseTensorInj.Certify.lemma_42
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:38:14.200821+00:00
-- url     : https://prove2.me/theorems/6d8a83b6-d501-4276-b023-e7a15eba909a
-- title:
--   Lemma 42 — variance-sensitive norm bound for symmetric matrices with independent subgaussian entries
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $N\ge1$, $\sigma,\gamma>0$, and let $M$ be an $N\times N$ symmetric random matrix whose upper-triangular entries $M_{ij}$, $i\le j$, are independent and centered with $\mathbb E[M_{ij}^2]\le\sigma^2$ and $\|M_{ij}\|_{\psi_2}\le\gamma$. Then with probability at least $1-N^{-3}$,
--   $$\|M\|_{\mathrm{op}}\le C\Big(\sigma\sqrt N+\gamma\sqrt{\log(1+\gamma^2/\sigma^2)}\sqrt{\log N}\Big).$$
--   The leading term depends only on the variance $\sigma^2$, not on the subgaussian parameter $\gamma$. Applied to the $(2q)!/2$ blocks of the flattening (Construction 39, Claim 40), it gives the utility bound of Proposition 36.
--
--   Differences from the source:
--
--   - encoding: an N × N matrix with failure probability N^{-c} → 1 ≤ N; reason: N^{-c} is undefined at N = 0
--   - encoding: σ, γ with positivity implicit (γ²/σ² and the ψ2 bound appear) → 0 < σ and 0 < γ; reason: the paper's standing parameters σ, γ > 0 (§3, Definition 3)
--   - reading: the upper-triangular entries of a symmetric matrix → the entries (i, j) with i ≤ j, diagonal included; reason: they determine the symmetric matrix, as in [BvH16]
--   - encoding: ‖χ‖_ψ2 ≤ γ, with ‖χ‖_ψ2 = inf{t > 0 : E exp(χ²/t²) ≤ 2} → Psi2Le P χ γ: exp(χ²/γ²) is integrable and E exp(χ²/γ²) ≤ 2 (with γ > 0); reason: for γ > 0 the two are equivalent: t ↦ E exp(χ²/t²) is non-increasing and right-continuous by monotone convergence
--   - encoding: with probability at least 1 − N^{-3}, ‖M‖_op ≤ C(…) → the outer probability of the complementary event is at most N^{-3}; reason: complement of the event; identical for the measurable events involved
--   - encoding: random variables on an unspecified probability space → every probability space (Ω : Type, P) with IsProbabilityMeasure P; reason: any joint law of finitely many real variables is realized on such a space; Lean universe convention
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 23, Lemma 42

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_RandomModel

open MeasureTheory ProbabilityTheory

namespace SparseTensorInj.Certify

/-- Lemma 42 (p. 23): there is a universal `C > 0` such that for every `N × N` symmetric random
matrix `M` whose upper-triangular entries (`i ≤ j`) are independent and centered with
`E[M_ij^2] ≤ σ^2` and `‖M_ij‖_{ψ2} ≤ γ`, with probability at least `1 − N^{-3}`,
`‖M‖_op ≤ C (σ √N + γ √(log(1 + γ^2/σ^2)) √(log N))`. -/
theorem lemma_42 : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (σ γ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (M : Ω → Matrix (Fin N) (Fin N) ℝ),
      1 ≤ N → 0 < σ → 0 < γ →
      (∀ ω, (M ω).IsSymm) →
      (∀ i j, Measurable fun ω => M ω i j) →
      iIndepFun (fun p : {p : Fin N × Fin N // p.1 ≤ p.2} => fun ω => M ω p.1.1 p.1.2) P →
      (∀ i j, i ≤ j → ∫ ω, M ω i j ∂P = 0) →
      (∀ i j, i ≤ j → ∫ ω, M ω i j ^ 2 ∂P ≤ σ ^ 2) →
      (∀ i j, i ≤ j → Psi2Le P (fun ω => M ω i j) γ) →
      P {ω | C * (σ * Real.sqrt N +
          γ * Real.sqrt (Real.log (1 + γ ^ 2 / σ ^ 2)) * Real.sqrt (Real.log N)) <
          opNorm (M ω)} ≤
        ENNReal.ofReal (((N : ℝ) ^ 3)⁻¹) := by sorry

end SparseTensorInj.Certify
