-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_mem_leftNeighborhood_iff_inducedDegree_pos
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.mem_leftNeighborhood_iff_inducedDegree_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:21:09.021473+00:00
-- url     : https://prove2.me/theorems/688c123e-dd68-43d1-9492-49e29cb3899c
-- title:
--   Biregular Bipartite Graph: mem left Neighborhood iff induced Degree pos
-- statement:
--   The Biregular Bipartite Graph construction uses the mem left Neighborhood iff induced Degree pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L94-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L94-L103

import Definitions.Def_QEC_Coding_HypergraphProduct_Diagonal
import Definitions.Def_QEC_Coding_ExpanderCodes_QuantumExpander
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumExpander
open QEC.Coding.HypergraphProduct
open scoped ENNReal
universe u
open QEC.Coding.QuantumExpander.BiregularBipartiteGraph
variable {A B : Type u}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.mem_leftNeighborhood_iff_inducedDegree_pos
    (G : BiregularBipartiteGraph A B) (S : Finset A) (b : B) :
    b ∈ G.leftNeighborhood S ↔ 0 < G.leftInducedDegree S b := by sorry
