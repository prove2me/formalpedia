-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_graphBoundary_range_eq_totalParity_ker
-- name    : QEC.Coding.BDL26TannerLocalRegularity.graphBoundary_range_eq_totalParity_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:28:07.896912+00:00
-- url     : https://prove2.me/theorems/2dff51f7-677f-4f23-b726-5d790e91fada
-- title:
--   BDL26 Tanner Local Regularity: graph Boundary range eq total Parity ker
-- statement:
--   Constructive connectedness proves binary graph exactness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L264-L281
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L264-L281

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26TannerLocalRegularity
open Module
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
universe u

theorem QEC.Coding.BDL26TannerLocalRegularity.graphBoundary_range_eq_totalParity_ker {Vertex Edge : Type}
    [Fintype Vertex] [Fintype Edge]
    [DecidableEq Vertex] [DecidableEq Edge]
    (edgeStart edgeEnd : Edge → Vertex) (root : Vertex)
    (paths : ∀ vertex, UndirectedPath edgeStart edgeEnd root vertex) :
    LinearMap.range (graphBoundary edgeStart edgeEnd) =
      LinearMap.ker totalParity := by sorry
