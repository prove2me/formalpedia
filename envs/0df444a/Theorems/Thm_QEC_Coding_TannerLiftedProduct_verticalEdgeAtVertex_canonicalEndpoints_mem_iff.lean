-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalEdgeAtVertex_canonicalEndpoints_mem_iff
-- name    : QEC.Coding.TannerLiftedProduct.verticalEdgeAtVertex_canonicalEndpoints_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:00:07.094269+00:00
-- url     : https://prove2.me/theorems/ec22f2be-dd01-449b-82cf-65d5dafff3dc
-- title:
--   Tanner Lifted Product: vertical Edge At Vertex canonical Endpoints mem iff
-- statement:
--   The canonical endpoints of the physical edge `(v,b)` are exactly `v`
--   and its vertical neighbour, possibly in the opposite order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L658-L669
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L658-L669

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
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [Fintype W] [DecidableEq W]
    [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.verticalEdgeAtVertex_canonicalEndpoints_mem_iff
    (label : W → G) (L : Finset (VertexIndex G))
    (v : VertexIndex G) (b : W) :
    (verticalEdgeEndpoint label (verticalEdgeAtVertex label v b) 0 ∈ L ∨
      verticalNeighbor label
        (verticalEdgeEndpoint label (verticalEdgeAtVertex label v b) 0) b ∈
          L) ↔
      v ∈ L ∨ verticalNeighbor label v b ∈ L := by sorry
