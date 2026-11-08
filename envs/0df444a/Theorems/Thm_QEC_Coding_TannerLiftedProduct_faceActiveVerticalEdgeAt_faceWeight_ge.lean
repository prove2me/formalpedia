-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceActiveVerticalEdgeAt_faceWeight_ge
-- name    : QEC.Coding.TannerLiftedProduct.faceActiveVerticalEdgeAt_faceWeight_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:03:57.323759+00:00
-- url     : https://prove2.me/theorems/10fca263-7018-42ff-bbd9-b9eaaef4e4a6
-- title:
--   Tanner Lifted Product: face Active Vertical Edge At face Weight ge
-- statement:
--   Endpoint-indexed form of `lemma:face-active-edge`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L770-L814
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L770-L814

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

theorem QEC.Coding.TannerLiftedProduct.faceActiveVerticalEdgeAt_faceWeight_ge
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d : Nat)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (v : VertexIndex G) (b : W)
    (he : IsFaceActiveVerticalEdgeAt label c v b) :
    d ≤ HammingWeight
      (ProductExpansion.row (localFaceMatrix label c v) b) := by sorry
