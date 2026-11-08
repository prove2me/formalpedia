-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_semanticPresentation_boundedLocality
-- name    : QEC.Coding.TannerLiftedProduct.semanticPresentation_boundedLocality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:13:18.81208+00:00
-- url     : https://prove2.me/theorems/0c7c1249-ce10-4ec3-b0ac-a8dc9a3d8c1b
-- title:
--   Tanner Lifted Product: semantic Presentation bounded Locality
-- statement:
--   The concrete local qudit checks of the Tanner lifted product have a
--   group-size-independent locality bound. Listing all scalar multiples costs one
--   fixed factor `|F|` in variable degree and leaves check weight unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L589-L609
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLiftedProduct.lean#L589-L609

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe w
variable {F G W R R' : Type w}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_68799ef5cb_575

theorem QEC.Coding.TannerLiftedProduct.semanticPresentation_boundedLocality
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F) :
    BoundedLocality
      (semanticPresentation label h g').localityProfile
      (2 * (Fintype.card W + Fintype.card R + Fintype.card R') *
        Fintype.card F) := by sorry
