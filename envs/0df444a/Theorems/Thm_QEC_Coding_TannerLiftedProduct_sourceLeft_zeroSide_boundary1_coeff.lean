-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_sourceLeft_zeroSide_boundary1_coeff
-- name    : QEC.Coding.TannerLiftedProduct.sourceLeft_zeroSide_boundary1_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:13:04.075723+00:00
-- url     : https://prove2.me/theorems/daac3bff-528c-4a10-ac64-b9249b0f92f1
-- title:
--   Tanner Lifted Product: source Left zero Side boundary1 coeff
-- statement:
--   The same coordinate inversion sends the zero-side endpoint to `g`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L105-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L105-L114

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.LiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [DecidableEq G]

theorem QEC.Coding.TannerLiftedProduct.sourceLeft_zeroSide_boundary1_coeff
    (sourceVoltage : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (r : R) (j br : W) (g : G) :
    LiftedProduct.boundary1Matrix
        (data (fun j => (sourceVoltage j)⁻¹) h g')
        ((0, r), br, g⁻¹)
        (Sum.inl (j, br, g⁻¹)) = h r j := by sorry
