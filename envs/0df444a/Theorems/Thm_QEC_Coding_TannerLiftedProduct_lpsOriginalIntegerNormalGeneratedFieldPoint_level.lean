-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGeneratedFieldPoint_level
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGeneratedFieldPoint_level
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:12:34.647972+00:00
-- url     : https://prove2.me/theorems/fe1565f0-511c-403a-b3bd-a442e5c880b9
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Generated Field Point level
-- statement:
--   Literal original field points commute with the actual finite integral level morphism.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L152-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean#L152-L188

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGeneratedFieldPoint_level
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Spec.map (CommRingCat.ofHom
      (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom) ≫
      lpsOriginalIntegerNormalGeneratedFieldPoint N hN =
    lpsOriginalIntegerNormalGeneratedFieldPoint M hM ≫
      lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM := by sorry
