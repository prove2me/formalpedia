-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_horizontalVertexEndpoints_le_two
-- name    : QEC.Coding.TannerLiftedProduct.card_horizontalVertexEndpoints_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:39:21.909224+00:00
-- url     : https://prove2.me/theorems/6d833aeb-97fc-4d24-ace9-e655913f5d82
-- title:
--   Tanner Lifted Product: card horizontal Vertex Endpoints le two
-- statement:
--   The Tanner Lifted Product construction uses the card horizontal Vertex Endpoints le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1186-L1191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L1186-L1191

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
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [Fintype W] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.card_horizontalVertexEndpoints_le_two
    (label : W → G) (v : VertexIndex G) (a : W) :
    (horizontalVertexEndpoints label v a).card ≤ 2 := by sorry
