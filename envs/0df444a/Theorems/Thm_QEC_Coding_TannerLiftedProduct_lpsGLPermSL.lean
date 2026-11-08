-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGLPermSL
-- name    : QEC.Coding.TannerLiftedProduct.lpsGLPermSL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:00:50.172242+00:00
-- url     : https://prove2.me/theorems/f6242fe8-5d20-4ce5-a683-05c6b952654f
-- title:
--   Tanner Lifted Product: lps GLPerm SL
-- statement:
--   The original integral modular action agrees with its true real GL realization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L40-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCommonDomain.lean#L40-L46

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsGLPermSL (γ : SL(2,ℤ)) :
    (MulAction.toPerm (Matrix.SpecialLinearGroup.mapGL ℝ γ) : Equiv.Perm ℍ)=
      (MulAction.toPerm γ : Equiv.Perm ℍ) := by sorry
