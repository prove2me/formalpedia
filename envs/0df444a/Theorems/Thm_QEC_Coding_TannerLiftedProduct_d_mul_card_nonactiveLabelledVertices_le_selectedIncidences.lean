-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_d_mul_card_nonactiveLabelledVertices_le_selectedIncidences
-- name    : QEC.Coding.TannerLiftedProduct.d_mul_card_nonactiveLabelledVertices_le_selectedIncidences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:04:13.323592+00:00
-- url     : https://prove2.me/theorems/9e94699d-f03b-44f2-baf6-1c50118e4190
-- title:
--   Tanner Lifted Product: d mul card nonactive Labelled Vertices le selected Incidences
-- statement:
--   Local-code distance gives at least `d` selected active-face incidences
--   for every non-active labelled vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L818-L859
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L818-L859

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

theorem QEC.Coding.TannerLiftedProduct.d_mul_card_nonactiveLabelledVertices_le_selectedIncidences
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d m : Nat)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x) :
    d * (nonactiveLabelledVertices label c m).card ≤
      (selectedFaceDirectionIncidences label c m).card := by sorry
