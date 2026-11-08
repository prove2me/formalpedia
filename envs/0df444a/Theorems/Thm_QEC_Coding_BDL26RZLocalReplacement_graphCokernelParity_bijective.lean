-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZLocalReplacement_graphCokernelParity_bijective
-- name    : QEC.Coding.BDL26RZLocalReplacement.graphCokernelParity_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:54:06.799605+00:00
-- url     : https://prove2.me/theorems/5242f920-6662-41da-a128-5d7299b260aa
-- title:
--   BDL26 RZLocal Replacement: graph Cokernel Parity bijective
-- statement:
--   Constructive graph connectedness makes the parity coordinate a bijection
--   on the boundary quotient.  Representatives are used only inside the proof; no
--   quotient section is exported.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16010-L16033
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZLocalReplacement.lean#L16010-L16033

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZLocalReplacement
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity

theorem QEC.Coding.BDL26RZLocalReplacement.graphCokernelParity_bijective {Vertex Edge : Type}
    [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex] [DecidableEq Edge]
    (edgeStart edgeEnd : Edge → Vertex) (root : Vertex)
    (paths : ∀ vertex, UndirectedPath edgeStart edgeEnd root vertex) :
    Function.Bijective (graphCokernelParity edgeStart edgeEnd) := by sorry
