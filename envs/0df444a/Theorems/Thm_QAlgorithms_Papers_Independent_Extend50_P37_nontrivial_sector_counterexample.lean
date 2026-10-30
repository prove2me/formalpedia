-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_nontrivial_sector_counterexample
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.nontrivial_sector_counterexample
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:46:12.0799+00:00
-- url     : https://prove2.me/theorems/9234e515-8042-42d7-9278-6758f024d514
-- title:
--   Appendix C: duality fails in a nontrivial permutation sector
-- statement:
--   On $\mathbb C^4=\mathbb C^2_L\otimes\mathbb C^2_R$, let $G=U(2)_L\otimes I_R$ and $K=I_L\otimes U(2)_R$, which are mutual centralizers. On the entire standard $S_3$-isotypic component $\mathcal H_{(2,1)}$ of three copies,
--   $$\operatorname{Alg}(Q(K)|_{(2,1)})\subsetneq
--   \operatorname{Comm}(Q(G)|_{(2,1)})\cap\operatorname{Comm}(P(S_3)|_{(2,1)}).$$
--   The projector is computed from the standard character $(2,0,-1)$ on the three conjugacy classes. This supplies a concrete failure of the proposed extension beyond the two one-dimensional sectors; it concerns ordinary tensor powers, not mixed tensor towers.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 37, Appendix C: duality fails in a nontrivial permutation sector

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- PDF pp.37-39, Appendix C: on the entire standard S3 isotypic component
of (C4)^tensor 3, the conjectured permutationally invariant commutant is
strictly larger. Correct the printed Pi_plus/minus on p.37 to Pi_lambda. -/
theorem nontrivial_sector_counterexample :
    unitaryCentralizer leftUnitaryGroup = rightUnitaryGroup ∧
    unitaryCentralizer rightUnitaryGroup = leftUnitaryGroup ∧
    cornerAlg (standardSector (Fin 2 × Fin 2)) (collectiveImage 3 rightUnitaryGroup) ⊂
      (cornerComm (standardSector (Fin 2 × Fin 2)) (collectiveImage 3 leftUnitaryGroup) ∩
        cornerComm (standardSector (Fin 2 × Fin 2)) (permutations (Fin 2 × Fin 2) 3)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
