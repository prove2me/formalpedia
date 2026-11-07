-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_exists_left_unique_neighbor
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.exists_left_unique_neighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:23:52.700371+00:00
-- url     : https://prove2.me/theorems/e21bf2af-2618-42a0-8164-502c84d18438
-- title:
--   Biregular Bipartite Graph: exists left unique neighbor
-- statement:
--   A nonempty set below the LTZ15 expansion threshold has a unique right
--   neighbor when the expansion defect is strictly below one half.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L151-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L151-L179

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

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.exists_left_unique_neighbor
    (G : BiregularBipartiteGraph A B) {γ δ : Real}
    (hExpand : G.LeftExpanding γ δ) (hδ : δ < 1 / 2)
    (S : Finset A) (hS : S.Nonempty)
    (hSmall : (S.card : Real) ≤ γ * Fintype.card A) :
    ∃ b, G.leftInducedDegree S b = 1 := by sorry
