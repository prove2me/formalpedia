-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_localFaceSupport_map_subset_faceSupport
-- name    : QEC.Coding.TannerLiftedProduct.localFaceSupport_map_subset_faceSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:44:32.254284+00:00
-- url     : https://prove2.me/theorems/0a69b474-c766-452b-916c-5ffc71a28be2
-- title:
--   Tanner Lifted Product: local Face Support map subset face Support
-- statement:
--   Local face support maps into the global active-face support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L900-L912
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerBlockWeight.lean#L900-L912

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [DecidableEq G] [DecidableEq W] [Fintype R]
    [DecidableEq R] [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.localFaceSupport_map_subset_faceSupport
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (v : VertexIndex G) :
    (localFaceSupport label c v).map (faceAtVertexEmbedding label v) ⊆
      faceSupport c := by sorry
