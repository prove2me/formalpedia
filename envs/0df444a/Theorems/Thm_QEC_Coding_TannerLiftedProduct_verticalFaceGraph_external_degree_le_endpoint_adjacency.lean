-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalFaceGraph_external_degree_le_endpoint_adjacency
-- name    : QEC.Coding.TannerLiftedProduct.verticalFaceGraph_external_degree_le_endpoint_adjacency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:04:07.807935+00:00
-- url     : https://prove2.me/theorems/7f76c702-e783-402b-ab0b-eb894932a9c7
-- title:
--   Tanner Lifted Product: vertical Face Graph external degree le endpoint adjacency
-- statement:
--   Face-neighbours that are active but not wholly unlabelled are counted by
--   horizontal labelled-neighbour directions at the two endpoints.  Since the
--   product adjacency graph also contains those horizontal directions, this is
--   the incidence bound used in `lemma:lbl-edge`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L926-L996
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerLabelledEdges.lean#L926-L996

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
omit [Fintype F] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.verticalFaceGraph_external_degree_le_endpoint_adjacency
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G)) (e : VerticalEdgeIndex W G) :
    (∑ e' ∈ activeVerticalEdges label c \
        unlabelledActiveVerticalEdges label c L,
        verticalFaceGraph label e e') ≤
      (∑ u ∈ L,
        adjacencyGraph label (verticalEdgeEndpoint label e 0) u) +
      ∑ u ∈ L, adjacencyGraph label
        (verticalNeighbor label (verticalEdgeEndpoint label e 0) e.2.1) u := by sorry
