-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_hermitian_marginals_extend
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.hermitian_marginals_extend
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T13:52:02.168459+00:00
-- url     : https://prove2.me/theorems/1b600d75-0eac-4746-a0a3-4a26771aa575
-- title:
--   Proposition II.2: consistent Hermitian marginals extend
-- statement:
--   Let $H_A,H_B,H_C$ be nonzero finite-dimensional complex Hilbert spaces. Let $Q_{AB}$ and $Q_{AC}$ be Hermitian operators of trace one satisfying $\operatorname{Tr}_B Q_{AB}=\operatorname{Tr}_C Q_{AC}$. Then there is a Hermitian trace-one operator $Q$ on $ABC$ such that
--   $$\operatorname{Tr}_C Q=Q_{AB},\qquad \operatorname{Tr}_B Q=Q_{AC}.$$
--   Positivity is deliberately not asserted: the result isolates positivity as the compatibility obstruction.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 3, Proposition II.2: consistent Hermitian marginals extend

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Proposition II.2, PDF p.3: Hermitian extension needs consistency but no positivity. -/
theorem hermitian_marginals_extend {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Nonempty I] [Nonempty J] [Nonempty K]
    (A : Op (I × J)) (B : Op (I × K))
    (hA : A.IsHermitian) (hB : B.IsHermitian) (htA : A.trace = 1) (htB : B.trace = 1)
    (hconsistent : traceRight A = traceRight B) :
    ∃ X : Op (I × J × K), X.IsHermitian ∧ X.trace = 1 ∧ (idTensorSuperop traceRight) X = A ∧ (idTensorSuperop traceLeft) X = B := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
