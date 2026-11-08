-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_graphBoundary_pathChain
-- name    : QEC.Coding.BDL26TannerLocalRegularity.graphBoundary_pathChain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:28:26.911733+00:00
-- url     : https://prove2.me/theorems/31db71ab-10fd-4a74-82d1-11a89cb884b9
-- title:
--   BDL26 Tanner Local Regularity: graph Boundary path Chain
-- statement:
--   A path chain has exactly its root and target as boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L157-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L157-L188

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

theorem QEC.Coding.BDL26TannerLocalRegularity.graphBoundary_pathChain {Vertex Edge : Type}
    [Fintype Edge] [DecidableEq Edge] [DecidableEq Vertex]
    (edgeStart edgeEnd : Edge → Vertex) (root : Vertex)
    {target : Vertex}
    (path : UndirectedPath edgeStart edgeEnd root target) :
    graphBoundary edgeStart edgeEnd (pathChain path) =
      Pi.single root 1 + Pi.single target 1 := by sorry
