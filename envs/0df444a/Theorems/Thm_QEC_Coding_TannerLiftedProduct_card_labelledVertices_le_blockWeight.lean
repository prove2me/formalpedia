-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_labelledVertices_le_blockWeight
-- name    : QEC.Coding.TannerLiftedProduct.card_labelledVertices_le_blockWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:04:00.863195+00:00
-- url     : https://prove2.me/theorems/0d37ade1-e98d-4c35-86c1-197c9a41d716
-- title:
--   Tanner Lifted Product: card labelled Vertices le block Weight
-- statement:
--   Source bound `|L| ≤ |c|`: when the first local-code distance is at least
--   four, the canonical labelled set is no larger than the PK22 block support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L883-L919
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L883-L919

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

theorem QEC.Coding.TannerLiftedProduct.card_labelledVertices_le_blockWeight
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d m : Nat)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (hFour : 4 ≤ d) :
    (labelledVertices label c m).card ≤ blockWeight c := by sorry
