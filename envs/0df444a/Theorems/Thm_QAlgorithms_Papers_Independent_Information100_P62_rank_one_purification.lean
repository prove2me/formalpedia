-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_rank_one_purification
-- name    : QAlgorithms.Papers.Independent.Information100.P62.rank_one_purification
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T22:02:27.410914+00:00
-- url     : https://prove2.me/theorems/40fd59b1-ad32-4e0f-baf6-177813998725
-- title:
--   Lemma B.2: rank-one purification rigidity
-- statement:
--   Let nonzero $u,v\in\mathbb C^2\otimes G$ satisfy
--   $$\operatorname{Tr}_{\mathbb C^2}|u\rangle\langle u|=\operatorname{Tr}_{\mathbb C^2}|v\rangle\langle v|,\qquad\operatorname{Tr}_{\mathbb C^2}|u\rangle\langle v|=0.$$
--   Then there are $g\ne0$ in $G$ and orthogonal unit vectors $x,y\in\mathbb C^2$ such that $u=x\otimes g$ and $v=y\otimes g$. No unit-norm assumption is imposed on $u,v$; their common norm is carried by $g$. The traced factor is specifically two-dimensional.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 61, Lemma B.2: rank-one purification rigidity

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.61, 62, Lemma B.2: rank-one purification rigidity. -/
theorem rank_one_purification (g : ℕ) (hg : 0 < g)
    (u v : EuclideanSpace ℂ (Fin 2 × Fin g)) (hu : u ≠ 0) (hv : v ≠ 0)
    (heq : partialCross u u = partialCross v v) (hcross : partialCross u v = 0) :
    ∃ w : EuclideanSpace ℂ (Fin g), w ≠ 0 ∧
      ∃ x y : EuclideanSpace ℂ (Fin 2), IsState x ∧ IsState y ∧ inner ℂ x y = 0 ∧
        u = tensorVec x w ∧ v = tensorVec y w := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
