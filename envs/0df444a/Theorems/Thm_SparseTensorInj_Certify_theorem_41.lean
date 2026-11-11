-- Prove2me | Theorems.Thm_SparseTensorInj_Certify_theorem_41
-- name    : SparseTensorInj.Certify.theorem_41
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:37:17.405202+00:00
-- url     : https://prove2.me/theorems/07124dcf-cc44-49df-a1a4-7ea8c0038a5b
-- title:
--   Theorem 41 ([BvH16]) — norm of a symmetric random matrix with independent bounded entries
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $N\ge1$, $s>0$, $K\in\mathbb R$, and let $X$ be an $N\times N$ symmetric random matrix whose upper-triangular entries $X_{ij}$, $i\le j$, are independent and centered with $\mathbb E[X_{ij}^2]\le s^2$ and $|X_{ij}|\le K$ almost surely. Then
--   $$\Pr\Big[\|X\|_{\mathrm{op}}\ge C\big(s\sqrt N+K\sqrt{\log N}\big)\Big]\le N^{-5}.$$
--   This is Corollary 3.12 with Remark 3.13 of Bandeira and van Handel [BvH16], cited by the paper; it is applied to truncated matrices in the proof of Lemma 42 (the even-order branch).
--
--   Differences from the source:
--
--   - reading: s with no stated sign → 0 < s; reason: s is the standard-deviation scale (in the paper's use s = σ > 0, the standing parameter of §3); excluding s ≤ 0 removes only instances where X = 0 almost surely (s = 0) or the threshold can be negative (s < 0), and at s = K = 0 the printed '≥' event has probability 1 > N^{-5} (INSIGHTS.yaml I2); K needs no sign hypothesis (|X_ij| ≤ K a.s. already forces K ≥ 0)
--   - encoding: an N × N matrix with failure probability N^{-c} → 1 ≤ N; reason: N^{-c} is undefined at N = 0
--   - reading: the upper-triangular entries of a symmetric matrix → the entries (i, j) with i ≤ j, diagonal included; reason: they determine the symmetric matrix, as in [BvH16]
--   - encoding: random variables on an unspecified probability space → every probability space (Ω : Type, P) with IsProbabilityMeasure P; reason: any joint law of finitely many real variables is realized on such a space; Lean universe convention
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 23, Theorem 41 (cited: [BvH16], Corollary 3.12 and Remark 3.13)

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_Tensor

open MeasureTheory ProbabilityTheory

namespace SparseTensorInj.Certify

/-- Theorem 41 (Corollary 3.12, Remark 3.13 in [BvH16]; p. 23): there is a universal `C > 0`
such that for every `N × N` symmetric random matrix `X` whose upper-triangular entries
(`i ≤ j`) are independent, centered, with `E[X_ij^2] ≤ s^2` (`s > 0`) and `|X_ij| ≤ K` almost
surely, `Pr[‖X‖_op ≥ C (s √N + K √(log N))] ≤ N^{-5}`. -/
theorem theorem_41 : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (s K : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → Matrix (Fin N) (Fin N) ℝ),
      1 ≤ N → 0 < s →
      (∀ ω, (X ω).IsSymm) →
      (∀ i j, Measurable fun ω => X ω i j) →
      iIndepFun (fun p : {p : Fin N × Fin N // p.1 ≤ p.2} => fun ω => X ω p.1.1 p.1.2) P →
      (∀ i j, i ≤ j → ∫ ω, X ω i j ∂P = 0) →
      (∀ i j, i ≤ j → ∫ ω, X ω i j ^ 2 ∂P ≤ s ^ 2) →
      (∀ i j, i ≤ j → ∀ᵐ ω ∂P, |X ω i j| ≤ K) →
      P {ω | C * (s * Real.sqrt N + K * Real.sqrt (Real.log N)) ≤ opNorm (X ω)} ≤
        ENNReal.ofReal (((N : ℝ) ^ 5)⁻¹) := by sorry

end SparseTensorInj.Certify
