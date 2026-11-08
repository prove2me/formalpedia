-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_d_mul_card_nonactiveLabelledVertices_le_four_mul_faceSupport
-- name    : QEC.Coding.TannerLiftedProduct.d_mul_card_nonactiveLabelledVertices_le_four_mul_faceSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:04:04.887633+00:00
-- url     : https://prove2.me/theorems/3a46774a-7a66-49d4-a04d-3fec2a5cd44e
-- title:
--   Tanner Lifted Product: d mul card nonactive Labelled Vertices le four mul face Support
-- statement:
--   Double counting active-face incidences bounds the non-active part of the
--   canonical labelled closure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L863-L879
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L863-L879

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

theorem QEC.Coding.TannerLiftedProduct.d_mul_card_nonactiveLabelledVertices_le_four_mul_faceSupport
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d m : Nat)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x) :
    d * (nonactiveLabelledVertices label c m).card ≤
      4 * (faceSupport c).card := by sorry
