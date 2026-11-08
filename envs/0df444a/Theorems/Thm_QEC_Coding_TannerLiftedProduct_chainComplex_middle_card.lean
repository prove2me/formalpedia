-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_chainComplex_middle_card
-- name    : QEC.Coding.TannerLiftedProduct.chainComplex_middle_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:12:36.38828+00:00
-- url     : https://prove2.me/theorems/031a34e3-133f-4682-8681-6d908ccdca18
-- title:
--   Tanner Lifted Product: chain Complex middle card
-- statement:
--   The lifted-product chain complex has the same middle-cell count as the
--   paper's face-plus-vertex decomposition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L151-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L151-L156

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
omit [Field F] [Fintype F] [Group G] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.chainComplex_middle_card :
    Fintype.card
        (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) =
      Fintype.card G *
        (Fintype.card W ^ 2 + 4 * Fintype.card R * Fintype.card R') := by sorry
