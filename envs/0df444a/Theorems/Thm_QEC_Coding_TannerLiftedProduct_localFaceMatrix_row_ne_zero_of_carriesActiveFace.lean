-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_localFaceMatrix_row_ne_zero_of_carriesActiveFace
-- name    : QEC.Coding.TannerLiftedProduct.localFaceMatrix_row_ne_zero_of_carriesActiveFace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:03:45.030505+00:00
-- url     : https://prove2.me/theorems/5c5a1d70-0bab-4296-a4f0-ae3df28a4d6b
-- title:
--   Tanner Lifted Product: local Face Matrix row ne zero of carries Active Face
-- statement:
--   A vertical edge that carries an active face has a nonzero local face
--   row.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L734-L745
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L734-L745

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
omit [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    [Fintype W] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.localFaceMatrix_row_ne_zero_of_carriesActiveFace
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (e : VerticalEdgeIndex W G)
    (he : CarriesActiveFaceVerticalEdge label c e) :
    ProductExpansion.row
      (localFaceMatrix label c (verticalEdgeEndpoint label e 0)) e.2.1 ≠ 0 := by sorry
