-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_sourceLeft_oneSide_boundary1_coeff
-- name    : QEC.Coding.TannerLiftedProduct.sourceLeft_oneSide_boundary1_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:12:29.918741+00:00
-- url     : https://prove2.me/theorems/c4f54496-5234-4686-ae4b-81f0b75e92cb
-- title:
--   Tanner Lifted Product: source Left one Side boundary1 coeff
-- statement:
--   Under inversion of every group coordinate, the first boundary of the
--   generic lifted product realizes the paper's left-derived Tanner edge:
--   `e_j ⊗ g` has coefficient `h r j` at `v₂ ⊗ (sourceVoltage j * g)`.
--   The Lean label is the inverse of the source voltage because `boundary1Matrix`
--   uses the right regular representation for its first factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L92-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L92-L101

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

theorem QEC.Coding.TannerLiftedProduct.sourceLeft_oneSide_boundary1_coeff
    (sourceVoltage : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (r : R) (j br : W) (g : G) :
    LiftedProduct.boundary1Matrix
        (data (fun j => (sourceVoltage j)⁻¹) h g')
        ((1, r), br, (sourceVoltage j * g)⁻¹)
        (Sum.inl (j, br, g⁻¹)) = h r j := by sorry
