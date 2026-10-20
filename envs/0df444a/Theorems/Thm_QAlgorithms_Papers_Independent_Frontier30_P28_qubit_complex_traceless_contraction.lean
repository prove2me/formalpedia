-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P28_qubit_complex_traceless_contraction
-- name    : QAlgorithms.Papers.Independent.Frontier30.P28.qubit_complex_traceless_contraction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:22:09.589078+00:00
-- url     : https://prove2.me/theorems/6a3909c8-6195-49e9-b5c5-70e28ebed7f8
-- title:
--   Attained contractive maximum on complex traceless qubit matrices
-- statement:
--   Let $T:M_2\to M_2$ be positive, trace preserving, and complex linear, with ordinary trace. For every $1\le p\le\infty$, the following maximum exists and satisfies
--
--   $$
--   \max_{\substack{\operatorname{tr}A=0\\ \|A\|_p=1}}\|T(A)\|_p\le1.
--   $$
--
--   Here $A$ ranges over all complex $2\times2$ matrices, the finite-exponent norms are Schatten norms, and the infinity endpoint is the spectral operator norm. More explicitly, there is a trace-zero unit-norm matrix $A_*$ whose output norm is at most one and dominates the output norm of every other trace-zero unit-norm input.
--
--   This gives contraction for the full complex traceless qubit subspace. It does not claim that the attained maximum always equals one.
-- source:
--   Contractivity of positive and trace preserving maps under $L_p$ norms, arXiv:math-ph/0601063v1, PDF p. 6, Theorem III.2

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P28

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier30.P28

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P11 (IsUnital)

/-- Theorem III.2, source PDF p.6. The source writes a maximum on the traceless
unit sphere; both attainment and its upper bound are retained. There is no
Hermitian restriction and no assertion that the maximum equals one. -/
theorem qubit_complex_traceless_contraction
    (T : Lin 2 2) (hpos : IsPositiveMap T) (htrace : TracePreserving T)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    ∃ A : M 2, A.trace = 0 ∧ schattenNorm p A = 1 ∧
      schattenNorm p (T A) ≤ 1 ∧
      ∀ B : M 2, B.trace = 0 → schattenNorm p B = 1 →
        schattenNorm p (T B) ≤ schattenNorm p (T A) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P28

end
