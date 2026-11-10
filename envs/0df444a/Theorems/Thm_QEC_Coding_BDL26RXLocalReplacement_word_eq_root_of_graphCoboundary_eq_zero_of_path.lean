-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_word_eq_root_of_graphCoboundary_eq_zero_of_path
-- name    : QEC.Coding.BDL26RXLocalReplacement.word_eq_root_of_graphCoboundary_eq_zero_of_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:08:05.166915+00:00
-- url     : https://prove2.me/theorems/9530c578-06a3-4067-8bfc-49e06933980d
-- title:
--   BDL26 RXLocal Replacement: word eq root of graph Coboundary eq zero of path
-- statement:
--   A zero graph coboundary is constant along one supplied constructive path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21125-L21152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21125-L21152

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXLocalReplacement
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RXLocalReplacement
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
universe u

theorem QEC.Coding.BDL26RXLocalReplacement.word_eq_root_of_graphCoboundary_eq_zero_of_path
    {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge]
    [DecidableEq Vertex] [DecidableEq Edge]
    (edgeStart edgeEnd : Edge → Vertex) (root vertex : Vertex)
    (path : UndirectedPath edgeStart edgeEnd root vertex)
    (word : Word Field Vertex)
    (hword : wordLinearMapTranspose (graphBoundary edgeStart edgeEnd) word = 0) :
    word vertex = word root := by sorry
