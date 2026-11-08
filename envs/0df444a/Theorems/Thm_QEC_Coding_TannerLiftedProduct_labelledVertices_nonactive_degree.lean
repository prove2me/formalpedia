-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_labelledVertices_nonactive_degree
-- name    : QEC.Coding.TannerLiftedProduct.labelledVertices_nonactive_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:40:28.232195+00:00
-- url     : https://prove2.me/theorems/189ca920-4ae1-41b9-a094-ef404e6e8e7f
-- title:
--   Tanner Lifted Product: labelled Vertices nonactive degree
-- statement:
--   Every non-active vertex in the minimal labelled closure entered through
--   the degree rule, hence has at least `m` labelled neighbours.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L491-L526
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerGlobalExpansion.lean#L491-L526

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
omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R']

theorem QEC.Coding.TannerLiftedProduct.labelledVertices_nonactive_degree (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (m : Nat) (v : VertexIndex G)
    (hv : v ∈ labelledVertices label c m)
    (hvInactive : v ∉ vertexBlockSupport c) :
    m ≤ ∑ u ∈ labelledVertices label c m, adjacencyGraph label v u := by sorry
