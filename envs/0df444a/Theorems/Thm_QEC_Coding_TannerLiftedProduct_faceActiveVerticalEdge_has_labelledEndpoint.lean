-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceActiveVerticalEdge_has_labelledEndpoint
-- name    : QEC.Coding.TannerLiftedProduct.faceActiveVerticalEdge_has_labelledEndpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:04:21.831273+00:00
-- url     : https://prove2.me/theorems/a3623a3e-4161-49b0-b153-b445606e6371
-- title:
--   Tanner Lifted Product: face Active Vertical Edge has labelled Endpoint
-- statement:
--   Endpoint form of `lemma:lbl-edge`, ready for the canonical labelled-set
--   global expansion theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L1099-L1143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L1099-L1143

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

theorem QEC.Coding.TannerLiftedProduct.faceActiveVerticalEdge_has_labelledEndpoint
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d m radius : Nat) (lambda : ℝ)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (L : Finset (VertexIndex G))
    (hClosed : IsClosedLabelledSet label c m L)
    (hExpand : SmallSetExpansion.IsSmallSetEdgeExpanding
      (verticalFaceGraph label) radius lambda)
    (hActiveRadius : (activeVerticalEdges label c).card ≤ radius)
    (hThreshold : (2 * m : ℝ) + lambda ≤ d)
    (v : VertexIndex G) (b : W)
    (he : IsFaceActiveVerticalEdgeAt label c v b) :
    v ∈ L ∨ verticalNeighbor label v b ∈ L := by sorry
