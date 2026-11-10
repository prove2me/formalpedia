-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXLocalReplacement_word_eq_root_of_graphCoboundary_eq_zero
-- name    : QEC.Coding.BDL26RXLocalReplacement.word_eq_root_of_graphCoboundary_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:07:34.398946+00:00
-- url     : https://prove2.me/theorems/e15b45a9-667d-4c6b-8e2b-f36f79b300f6
-- title:
--   BDL26 RXLocal Replacement: word eq root of graph Coboundary eq zero
-- statement:
--   A zero graph coboundary makes a word constant along every constructive
--   undirected path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21091-L21122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXLocalReplacement.lean#L21091-L21122

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

theorem QEC.Coding.BDL26RXLocalReplacement.word_eq_root_of_graphCoboundary_eq_zero
    {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge]
    [DecidableEq Vertex] [DecidableEq Edge]
    (edgeStart edgeEnd : Edge → Vertex) (root : Vertex)
    (paths : ∀ vertex, UndirectedPath edgeStart edgeEnd root vertex)
    (word : Word Field Vertex)
    (hword : wordLinearMapTranspose (graphBoundary edgeStart edgeEnd) word = 0) :
    ∀ vertex, word vertex = word root := by sorry
