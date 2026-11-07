-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_mem_Q_of_mem_complex
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJNInFractionField_mem_Q_of_mem_complex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:24:05.837191+00:00
-- url     : https://prove2.me/theorems/7f21dc9f-ce69-48f7-98c4-ea8f60a501b2
-- title:
--   Tanner Lifted Product: lps Original JNIn Fraction Field mem Q of mem complex
-- statement:
--   Constructed descent of the SAME original generator from its actual complex field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L643-L706
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L643-L706

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJNInFractionField_mem_Q_of_mem_complex
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (hc : lpsOriginalJNInFractionField N hN ∈ lpsOriginalGeneratedFunctionField M hM) :
    lpsOriginalJNInFractionField N hN ∈ lpsOriginalGeneratedFunctionFieldQ M hM := by sorry
