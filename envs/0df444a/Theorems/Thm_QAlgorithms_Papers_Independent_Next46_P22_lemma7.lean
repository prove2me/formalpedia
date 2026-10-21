-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_lemma7
-- name    : QAlgorithms.Papers.Independent.Next46.P22.lemma7
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:47:58.942823+00:00
-- url     : https://prove2.me/theorems/7157c00e-032b-4077-b20b-e51b90deb7fa
-- title:
--   Lemma 7
-- statement:
--   Let $F$ be any field, $H$ any Hopf algebra over $F$ and $L$ a right $H$-comodule Lie algebra. If $M$ is an invariant $F$-subspace for the supplied structure, its centralizer
--
--   $$C_L(M)=\{a\in L:[a,b]=0\text{ for every }b\in M\}$$
--
--   is invariant too. The subspace $M$ need not be a Lie subalgebra or ideal. No characteristic, dimension, integral or semisimplicity hypothesis is imposed. The centralizer is unrelated to the nilpotent radical.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 11, Lemma 7

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- Lemma 7, PDF p.11: centralizer of an arbitrary subcomodule. -/
theorem lemma7 (rho : RightComodule F H L) (hr : ComoduleLie rho)
    (M : Submodule F L) (hM : CoStable rho M) :
    CoStable rho (Centralizer M) := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
