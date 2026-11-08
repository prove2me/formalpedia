-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_activeVerticalEdges_le
-- name    : QEC.Coding.TannerLiftedProduct.card_activeVerticalEdges_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:02:21.876692+00:00
-- url     : https://prove2.me/theorems/c026a742-9089-4709-ac6b-f263b5a6936f
-- title:
--   Tanner Lifted Product: card active Vertical Edges le
-- statement:
--   Active-edge cardinality before folding it into block weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L289-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L289-L322

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.card_activeVerticalEdges_le
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    (activeVerticalEdges label c).card ≤
      (vertexBlockSupport c).card * Fintype.card W +
        (faceSupport c).card * 2 := by sorry
