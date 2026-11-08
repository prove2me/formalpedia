-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_faceSupport_has_labelled_incidentVertex_of_carriesActiveFace
-- name    : QEC.Coding.TannerLiftedProduct.faceSupport_has_labelled_incidentVertex_of_carriesActiveFace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:40:41.230135+00:00
-- url     : https://prove2.me/theorems/54ebbeec-c0a8-4aba-9714-445b097d4a2e
-- title:
--   Tanner Lifted Product: face Support has labelled incident Vertex of carries Active Face
-- statement:
--   If every vertical edge carrying an active face has a labelled endpoint,
--   then every
--   active face belongs to the star of a labelled vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L533-L551
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L533-L551

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
omit [Fintype F] [DecidableEq G] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.faceSupport_has_labelled_incidentVertex_of_carriesActiveFace
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G))
    (hEdgeLabel : ∀ v b, CarriesActiveFaceVerticalEdgeAt label c v b →
      v ∈ L ∨ verticalNeighbor label v b ∈ L) :
    ∀ p ∈ faceSupport c, ∃ v ∈ L, p ∈ faceStar label v := by sorry
