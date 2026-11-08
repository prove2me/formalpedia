-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_graphBoundary_quotient_mk_eq_single_root_totalParity
-- name    : QEC.Coding.BDL26TannerLocalRegularity.graphBoundary_quotient_mk_eq_single_root_totalParity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:31:36.161046+00:00
-- url     : https://prove2.me/theorems/ba105cdd-7b85-4fee-a45c-ffa826800ac2
-- title:
--   BDL26 Tanner Local Regularity: graph Boundary quotient mk eq single root total Parity
-- statement:
--   In the boundary quotient, every word equals its explicit root-parity
--   representative.  This is an equality of quotient representatives only; it
--   does not define a section or a quotient equivalence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L238-L261
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L238-L261

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

theorem QEC.Coding.BDL26TannerLocalRegularity.graphBoundary_quotient_mk_eq_single_root_totalParity
    {Vertex Edge : Type}
    [Fintype Vertex] [Fintype Edge]
    [DecidableEq Vertex] [DecidableEq Edge]
    (edgeStart edgeEnd : Edge → Vertex) (root : Vertex)
    (paths : ∀ vertex, UndirectedPath edgeStart edgeEnd root vertex)
    (word : Word Field Vertex) :
    (LinearMap.range (graphBoundary edgeStart edgeEnd)).mkQ word =
      (LinearMap.range (graphBoundary edgeStart edgeEnd)).mkQ
        (Pi.single root (totalParity word)) := by sorry
