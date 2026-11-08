-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_activeFaceDirectionPairs
-- name    : QEC.Coding.TannerLiftedProduct.card_activeFaceDirectionPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:39:47.642864+00:00
-- url     : https://prove2.me/theorems/00ec6108-5219-42c3-9f8a-0e52066f359b
-- title:
--   Tanner Lifted Product: card active Face Direction Pairs
-- statement:
--   Rectangle weight is the cardinality of its active face-direction pairs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L139-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L139-L153

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
omit [Fintype F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.card_activeFaceDirectionPairs
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) (A B : Finset W) :
    (activeFaceDirectionPairs label c v A B).card =
      ProductExpansion.restrictedWeight (localFaceMatrix label c v) B A := by sorry
