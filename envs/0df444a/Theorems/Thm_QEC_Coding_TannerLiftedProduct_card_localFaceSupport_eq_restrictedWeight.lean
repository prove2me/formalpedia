-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_localFaceSupport_eq_restrictedWeight
-- name    : QEC.Coding.TannerLiftedProduct.card_localFaceSupport_eq_restrictedWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:45:10.633972+00:00
-- url     : https://prove2.me/theorems/f0b652df-37af-476d-98a8-70a90e08533c
-- title:
--   Tanner Lifted Product: card local Face Support eq restricted Weight
-- statement:
--   The number of active faces in a star is the full-rectangle weight of its
--   local face matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L918-L933
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L918-L933

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [Fintype G] [DecidableEq G] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.card_localFaceSupport_eq_restrictedWeight
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    (localFaceSupport label c v).card =
      ProductExpansion.restrictedWeight (localFaceMatrix label c v)
        Finset.univ Finset.univ := by sorry
