-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P07_exterior_separability
-- name    : QAlgorithms.Papers.Independent.Information100.P07.exterior_separability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:37:32.698591+00:00
-- url     : https://prove2.me/theorems/0be2b3bf-a5e0-4789-92e6-8252849e2930
-- title:
--   Lemma S5: wing coherence characterizes exterior separability
-- statement:
--   Let $P_A,P_B$ be rank-two orthogonal projectors on the two qutrit factors. Let $T\ge0$ be supported on the orthogonal complement of their product rectangle. Then
--   $$T\in\mathrm{SEP}\iff(P_A\otimes P_B^\perp)T(P_A^\perp\otimes P_B)=0.$$
--   Here SEP is the cone of separable positive operators, without trace normalization. The zero operator and singular wing and corner blocks are allowed. Coherences between either wing and the corner are unrestricted.
--
--   This is the exact exterior separability test.
-- source:
--   Complete Classification of Reversible Entanglement Transformations of Two Qutrits, arXiv:2610.05234v1, PDF p. 18, Lemma S5: wing coherence characterizes exterior separability

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P07

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Entanglement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2610.05234v1, PDF pp.18–19, Lemma S5: exact exterior separability test. -/
theorem exterior_separability (P Q : Local) (T : Joint)
    (hP : IsProjection P) (hQ : IsProjection Q) (hrP : P.rank = 2) (hrQ : Q.rank = 2)
    (hT : T.PosSemidef) (hsupp : (1 - Matrix.kronecker P Q) * T * (1 - Matrix.kronecker P Q) = T) :
    IsSeparablePositive T ↔ Matrix.kronecker P (1 - Q) * T * Matrix.kronecker (1 - P) Q = 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P07

end
