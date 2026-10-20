-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P28_positive_map_can_have_nonpositive_unital_part
-- name    : QAlgorithms.Papers.Independent.Frontier30.P28.positive_map_can_have_nonpositive_unital_part
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:20:34.008104+00:00
-- url     : https://prove2.me/theorems/8c4df901-7673-4479-bf0c-ba0042ec94b9
-- title:
--   A positive map can have a nonpositive constructed unital part
-- statement:
--   For some finite integer $n\ge3$, there is a positive trace-preserving complex-linear map $T:M_n\to M_n$ whose constructed unital part
--
--   $$
--   T_1(A)=T(A)-\frac{\operatorname{tr}A}{n}\bigl(T(I_n)-I_n\bigr)
--   $$
--
--   is not positive. Trace is the ordinary unnormalized trace.
--
--   This existence statement shows that positivity of the original map does not suffice for the conditional contraction criterion based on positivity of $T_1$. It makes no such assertion in dimension two.
-- source:
--   Contractivity of positive and trace preserving maps under $L_p$ norms, arXiv:math-ph/0601063v1, PDF p. 5, §III, last sentence

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P28

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier30.P28

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P11 (IsUnital)

/-- Unnumbered nonpositivity observation, source PDF p.5.
A positive trace-preserving map need not have positive constructed unital part;
this is existential and does not assert such an example in dimension two. -/
theorem positive_map_can_have_nonpositive_unital_part :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ T : Lin n n,
      IsPositiveMap T ∧ TracePreserving T ∧ ¬ IsPositiveMap (unitalPart T) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P28

end
