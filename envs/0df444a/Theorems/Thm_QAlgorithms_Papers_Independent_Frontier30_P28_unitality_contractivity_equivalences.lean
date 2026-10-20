-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P28_unitality_contractivity_equivalences
-- name    : QAlgorithms.Papers.Independent.Frontier30.P28.unitality_contractivity_equivalences
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:17:13.435602+00:00
-- url     : https://prove2.me/theorems/cff42f06-f7db-4620-a37f-fb6a0359d01c
-- title:
--   Four equivalent unitality and Schatten-contractivity conditions
-- statement:
--   Let $n\ge1$, and let $T:M_n\to M_n$ be a positive, trace-preserving complex-linear map, with ordinary trace. Let $I_n$ be the identity matrix and let $\|T\|_{p-p}$ denote the induced Schatten norm, using the spectral norm at infinity. The following four conditions are equivalent:
--
--   1. There is an exponent $1<p\le\infty$ for which $\|T(I_n)\|_p\le n^{1/p}$.
--   2. $T(I_n)=I_n$.
--   3. For every $1\le p\le\infty$, $\|T\|_{p-p}\le1$.
--   4. For some $1<p\le\infty$, $\|T\|_{p-p}\le1$.
--
--   $$
--   \text{(1)}\iff\text{(2)}\iff\text{(3)}\iff\text{(4)}.
--   $$
--
--   The two existential exponents may differ, and $n^{1/\infty}=1$. This characterizes contractivity beyond the trace endpoint for maps with equal input and output dimensions.
-- source:
--   Contractivity of positive and trace preserving maps under $L_p$ norms, arXiv:math-ph/0601063v1, PDF p. 3, Theorem II.4

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P28

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier30.P28

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P11 (IsUnital)

/-- Theorem II.4, source PDF p.3: all four equivalent conditions, for square
positive trace-preserving maps. The two existential exponents are independent. -/
theorem unitality_contractivity_equivalences
    (n : ℕ) (hn : 0 < n) (T : Lin n n)
    (hpos : IsPositiveMap T) (htrace : TracePreserving T) :
    ((∃ p : ℝ≥0∞, 1 < p ∧
        schattenNorm p (T 1) ≤ Real.rpow (n : ℝ) (inverseExponent p)) ↔
      IsUnital T) ∧
    (IsUnital T ↔ ∀ p : ℝ≥0∞, 1 ≤ p → inducedPNorm p T ≤ 1) ∧
    ((∀ p : ℝ≥0∞, 1 ≤ p → inducedPNorm p T ≤ 1) ↔
      ∃ p : ℝ≥0∞, 1 < p ∧ inducedPNorm p T ≤ 1) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P28

end
