-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_twiceBalanced_dimensionLowerBound
-- name    : QEC.Coding.ExpanderCodes.PK20.twiceBalanced_dimensionLowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:38:08.478059+00:00
-- url     : https://prove2.me/theorems/05fc8756-74aa-4ddf-9152-5ab7a8a16dd3
-- title:
--   PK20: twice Balanced dimension Lower Bound
-- statement:
--   Each classical kernel multiplies the encoded dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TwoStepBalancing.lean#L172-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TwoStepBalancing.lean#L172-L223

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Dimension
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_ExpanderCodes_TwoStepBalancing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.DistanceBalancing
universe u
variable {xZero xOne xTwo bitOne checkOne bitTwo checkTwo : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype bitOne] [DecidableEq bitOne]
variable [Fintype checkOne] [DecidableEq checkOne]
variable [Fintype bitTwo] [DecidableEq bitTwo]
variable [Fintype checkTwo] [DecidableEq checkTwo]

theorem QEC.Coding.ExpanderCodes.PK20.twiceBalanced_dimensionLowerBound
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y₁ : Word (ZMod 2) bitOne →ₗ[ZMod 2] Word (ZMod 2) checkOne)
    (Y₂ : Word (ZMod 2) bitTwo →ₗ[ZMod 2] Word (ZMod 2) checkTwo) :
    Module.finrank (ZMod 2) X.middleHomology *
        Module.finrank (ZMod 2) (LinearMap.ker Y₁) *
        Module.finrank (ZMod 2) (LinearMap.ker Y₂) ≤
      Module.finrank (ZMod 2)
        (twiceBalancedComplex X Y₁ Y₂).middleHomology := by sorry
