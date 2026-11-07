-- Prove2me | Theorems.Thm_QEC_Coding_QuantumExpander_BiregularBipartiteGraph_two_mul_leftNeighborhood_card_le_sum_of_no_unique
-- name    : QEC.Coding.QuantumExpander.BiregularBipartiteGraph.two_mul_leftNeighborhood_card_le_sum_of_no_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:22:21.559221+00:00
-- url     : https://prove2.me/theorems/84088dd3-24af-4221-8d0a-1702c281ec7f
-- title:
--   Biregular Bipartite Graph: two mul left Neighborhood card le sum of no unique
-- statement:
--   If every nonempty induced right degree is at least two, double counting
--   bounds twice the neighborhood size by the number of incident edges.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L119-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuantumExpander.lean#L119-L147

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

theorem QEC.Coding.QuantumExpander.BiregularBipartiteGraph.two_mul_leftNeighborhood_card_le_sum_of_no_unique
    (G : BiregularBipartiteGraph A B) (S : Finset A)
    (hNoUnique : ∀ b, G.leftInducedDegree S b ≠ 1) :
    2 * (G.leftNeighborhood S).card ≤
      ∑ b, G.leftInducedDegree S b := by sorry
