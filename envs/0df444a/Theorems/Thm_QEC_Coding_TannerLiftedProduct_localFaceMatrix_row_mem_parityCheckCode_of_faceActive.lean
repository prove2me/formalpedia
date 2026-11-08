-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_localFaceMatrix_row_mem_parityCheckCode_of_faceActive
-- name    : QEC.Coding.TannerLiftedProduct.localFaceMatrix_row_mem_parityCheckCode_of_faceActive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:03:50.223708+00:00
-- url     : https://prove2.me/theorems/c5cd4b53-b870-4e32-bffa-020012a39837
-- title:
--   Tanner Lifted Product: local Face Matrix row mem parity Check Code of face Active
-- statement:
--   On a face-active vertical edge the incident face row lies in the first
--   local code `ker h`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L691-L727
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L691-L727

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

theorem QEC.Coding.TannerLiftedProduct.localFaceMatrix_row_mem_parityCheckCode_of_faceActive
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (e : VerticalEdgeIndex W G)
    (he : IsFaceActiveVerticalEdge label c e) :
    ProductExpansion.row
        (localFaceMatrix label c (verticalEdgeEndpoint label e 0)) e.2.1 ∈
      (ProductExpansion.parityCheckCode h).carrier := by sorry
