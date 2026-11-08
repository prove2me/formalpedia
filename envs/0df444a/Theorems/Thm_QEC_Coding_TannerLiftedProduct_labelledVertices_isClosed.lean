-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_labelledVertices_isClosed
-- name    : QEC.Coding.TannerLiftedProduct.labelledVertices_isClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:36:28.946597+00:00
-- url     : https://prove2.me/theorems/8701abfb-11f0-4655-bc6c-c231d774d6e9
-- title:
--   Tanner Lifted Product: labelled Vertices is Closed
-- statement:
--   The intersection construction is itself closed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L471-L486
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L471-L486

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.labelledVertices_isClosed (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) :
    IsClosedLabelledSet label c m (labelledVertices label c m) := by sorry
