-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_example11
-- name    : QAlgorithms.Papers.Independent.Next46.P22.example11
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:41:34.08961+00:00
-- url     : https://prove2.me/theorems/6f5f4c65-6151-4eb9-8ff3-9957d81737b7
-- title:
--   Example 11
-- statement:
--   Let $F$ be any field, $H$ any Hopf algebra over $F$ and $L$ a right $H$-comodule Lie algebra with coaction $\rho$. With its adjoint representation, $L$ is a symmetric $(H,L)$-module. In Sweedler notation,
--
--   $$\rho([a,b])=\sum[a_0,b_0]\otimes a_1b_1=\sum[a_0,b_0]\otimes b_1a_1.$$
--
--   This includes ordinary comodule-module compatibility and its reversed coefficient order. No commutativity, integral or dimensional assumption on $H$ is needed.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 7, Example 11

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

/-- Example 11, PDF p.7: the adjoint representation is symmetric. -/
theorem example11 (rho : RightComodule F H L) (hr : ComoduleLie rho) :
    SymmetricComodule rho rho := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
