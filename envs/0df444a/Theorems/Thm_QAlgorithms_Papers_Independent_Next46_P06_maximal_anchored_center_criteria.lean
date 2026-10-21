-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_maximal_anchored_center_criteria
-- name    : QAlgorithms.Papers.Independent.Next46.P06.maximal_anchored_center_criteria
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:41:35.875385+00:00
-- url     : https://prove2.me/theorems/98d3bfaf-b400-47fe-8d70-ab66058b4437
-- title:
--   Remark 6.5
-- statement:
--   Let $F$ be a unital complex algebra, $E$ a possibly nonunital complex subalgebra, and $\rho:E\to\mathcal L(X)$ a nondegenerate representation on a complex Banach space. Let $Z(E)=\{d\in E:de=ed\text{ for all }e\in E\}$ and let $F_\rho=\langle E,F,\rho\rangle$. Then $f\in F_\rho$ whenever $Z(E)\cap[f]_E$ is an anchor. If $F$ is commutative, then
--
--   $$F_\rho=\{f\in F:[f]_E\text{ is a }\rho\text{-anchor}\}.$$
--
--   Both the sufficient center criterion and the commutative equality are asserted.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 16, Remark 6.5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

universe u v w

variable {F G : Type*} [Ring F] [Algebra ℂ F] [Ring G] [Algebra ℂ G]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Remark 6.5, PDF p.16: the center criterion and the equality in the
commutative case are both retained. -/
theorem maximal_anchored_center_criteria [CompleteSpace X] (rho : F → X →L[ℂ] X) (E : Set F)
    (hrho : AlgebraRepresentationOn rho E) (hnd : Nondegenerate rho E) :
    (∀ f, AnchorSet (representationGraphs rho) (setCenter E ∩ symbolBracket E f) →
      f ∈ maximalAnchored rho E) ∧
    ((∀ f g : F, f * g = g * f) →
      maximalAnchored rho E = {f | Anchored (representationGraphs rho) E f}) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
