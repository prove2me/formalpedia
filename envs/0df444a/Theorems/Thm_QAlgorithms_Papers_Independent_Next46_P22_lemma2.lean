-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_lemma2
-- name    : QAlgorithms.Papers.Independent.Next46.P22.lemma2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:39:14.103469+00:00
-- url     : https://prove2.me/theorems/69613b70-4547-4f8d-bf8e-a840ee48ccf3
-- title:
--   Lemma 2
-- statement:
--   Let $F$ be any field, $H$ any Hopf algebra over $F$, and $L$ a left $H$-module Lie algebra. For an ordinary Lie ideal $I$ define $HI=\operatorname{span}_F\{hi:h\in H,\ i\in I\}$. Then
--
--   $$[L,HI]\subseteq HI,\qquad H(HI)\subseteq HI.$$
--
--   Thus $HI$ is an $H$-invariant Lie ideal. Stability of $I$, an integral, dimension bounds and characteristic assumptions are not required.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 5, Lemma 2

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

/-- Lemma 2, PDF p.5: HI is an H-invariant ideal, with no prior invariance of I. -/
theorem lemma2 (alpha : H →ₐ[F] Module.End F L) (ha : ModuleLie alpha) (I : LieIdeal F L) :
    IdealSubspace (actionHull alpha I) ∧ ActionStable alpha (actionHull alpha I) := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
