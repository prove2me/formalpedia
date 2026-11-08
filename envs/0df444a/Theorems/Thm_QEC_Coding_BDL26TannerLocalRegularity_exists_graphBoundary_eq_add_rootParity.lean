-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TannerLocalRegularity_exists_graphBoundary_eq_add_rootParity
-- name    : QEC.Coding.BDL26TannerLocalRegularity.exists_graphBoundary_eq_add_rootParity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:28:17.491098+00:00
-- url     : https://prove2.me/theorems/9c4903e3-a690-4487-b210-288f272e8b49
-- title:
--   BDL26 Tanner Local Regularity: exists graph Boundary eq add root Parity
-- statement:
--   Every word differs from the root parity representative by an explicit
--   boundary.  The witness is local to the theorem; no global section is exported.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L192-L233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalRegularity.lean#L192-L233

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

theorem QEC.Coding.BDL26TannerLocalRegularity.exists_graphBoundary_eq_add_rootParity {Vertex Edge : Type}
    [Fintype Vertex] [Fintype Edge]
    [DecidableEq Vertex] [DecidableEq Edge]
    (edgeStart edgeEnd : Edge → Vertex) (root : Vertex)
    (paths : ∀ vertex, UndirectedPath edgeStart edgeEnd root vertex)
    (word : Word Field Vertex) :
    ∃ chain : Word Field Edge,
      graphBoundary edgeStart edgeEnd chain =
        word + Pi.single root (totalParity word) := by sorry
