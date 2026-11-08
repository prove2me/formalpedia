-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_unlabelledActiveVerticalEdges_subset_activeVerticalEdges
-- name    : QEC.Coding.TannerLiftedProduct.unlabelledActiveVerticalEdges_subset_activeVerticalEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:02:47.768201+00:00
-- url     : https://prove2.me/theorems/d6daf18b-c83d-4728-8e2c-78861564d3fc
-- title:
--   Tanner Lifted Product: unlabelled Active Vertical Edges subset active Vertical Edges
-- statement:
--   The Tanner Lifted Product construction uses the unlabelled Active Vertical Edges subset active Vertical Edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L563-L570
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L563-L570

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
omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.unlabelledActiveVerticalEdges_subset_activeVerticalEdges
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G)) :
    unlabelledActiveVerticalEdges label c L ⊆ activeVerticalEdges label c := by sorry
