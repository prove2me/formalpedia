-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_selectedFaceActiveDirection_spec
-- name    : QEC.Coding.TannerLiftedProduct.selectedFaceActiveDirection_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:02:57.250915+00:00
-- url     : https://prove2.me/theorems/938ca654-47e9-4a07-8144-aa6ca59a8172
-- title:
--   Tanner Lifted Product: selected Face Active Direction spec
-- statement:
--   The Tanner Lifted Product construction uses the selected Face Active Direction spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L455-L466
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L455-L466

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

theorem QEC.Coding.TannerLiftedProduct.selectedFaceActiveDirection_spec (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat)
    (v : {v // v ∈ nonactiveLabelledVertices label c m}) :
    IsFaceActiveVerticalEdgeAt label c v.1
      (selectedFaceActiveDirection label c m v) := by sorry
