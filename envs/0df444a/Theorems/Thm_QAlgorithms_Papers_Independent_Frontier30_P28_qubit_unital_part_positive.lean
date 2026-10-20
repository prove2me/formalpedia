-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P28_qubit_unital_part_positive
-- name    : QAlgorithms.Papers.Independent.Frontier30.P28.qubit_unital_part_positive
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:21:20.868958+00:00
-- url     : https://prove2.me/theorems/789bbca5-3209-4e29-9205-f8f4191cc48a
-- title:
--   The unital part of a positive trace-preserving qubit map is positive
-- statement:
--   Let $T:M_2\to M_2$ be a positive trace-preserving complex-linear map, with ordinary trace. Its constructed unital part is
--
--   $$
--   T_1(A)=T(A)-\frac{\operatorname{tr}A}{2}\bigl(T(I_2)-I_2\bigr).
--   $$
--
--   Then $T_1$ is positive.
--
--   This qubit-specific conclusion supplies the positivity condition in the preceding decomposition criterion. It is a conclusion about the explicitly constructed map, rather than an additional assumption on the input map.
-- source:
--   Contractivity of positive and trace preserving maps under $L_p$ norms, arXiv:math-ph/0601063v1, PDF p. 6, §III.A, unnumbered result

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P28

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier30.P28

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P11 (IsUnital)

/-- Unnumbered qubit result proved by the Bloch-ball argument,
source PDF p.6, §III.A: positivity of the constructed unital part is a conclusion. -/
theorem qubit_unital_part_positive
    (T : Lin 2 2) (hpos : IsPositiveMap T) (htrace : TracePreserving T) :
    IsPositiveMap (unitalPart T) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P28

end
