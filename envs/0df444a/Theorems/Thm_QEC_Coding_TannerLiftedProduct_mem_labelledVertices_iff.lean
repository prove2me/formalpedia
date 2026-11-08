-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_labelledVertices_iff
-- name    : QEC.Coding.TannerLiftedProduct.mem_labelledVertices_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:36:28.359108+00:00
-- url     : https://prove2.me/theorems/d04e7f60-74f3-4435-92ac-1e242b1f46b9
-- title:
--   Tanner Lifted Product: mem labelled Vertices iff
-- statement:
--   The Tanner Lifted Product construction uses the mem labelled Vertices iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L449-L456
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L449-L456

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

theorem QEC.Coding.TannerLiftedProduct.mem_labelledVertices_iff (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) (v : VertexIndex G) :
    v ∈ labelledVertices label c m ↔
      ∀ L, IsClosedLabelledSet label c m L → v ∈ L := by sorry
