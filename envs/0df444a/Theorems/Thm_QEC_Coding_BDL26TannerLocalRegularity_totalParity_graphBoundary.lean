-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_totalParity_graphBoundary
-- name    : QEC.Coding.BDL26TannerLocalRegularity.totalParity_graphBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:28:03.701457+00:00
-- url     : https://prove2.me/theorems/a940aca9-95ec-4a03-a224-132a228d107e
-- title:
--   BDL26 Tanner Local Regularity: total Parity graph Boundary
-- statement:
--   Every constructed graph boundary has even total parity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L141-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L141-L154

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

theorem QEC.Coding.BDL26TannerLocalRegularity.totalParity_graphBoundary {Vertex Edge : Type}
    [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex]
    (edgeStart edgeEnd : Edge → Vertex) (chain : Word Field Edge) :
    totalParity (graphBoundary edgeStart edgeEnd chain) = 0 := by sorry
