-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_optimum_le_two_mul_sum
-- name    : QuantumMaxCutEnergy.optimum_le_two_mul_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T16:56:39.307624+00:00
-- url     : https://prove2.me/theorems/89736754-7c59-4391-a8db-aad2f55568fb
-- title:
--   Crude two-sided bound: the Quantum Max-Cut optimum is at most twice the total weight
-- statement:
--   For every weighted graph $G$ in the campaign's input format, the Quantum Max-Cut optimum is at most twice the total edge weight $W(G)=\sum_e w_e$.
--
--   The proof bounds each edge term: for a normalized state the squared differences along an edge sum to at most $4$, because $|a-b|^2\le 2|a|^2+2|b|^2$ and the edge involution permutes the basis states. Hence the energy is at most $\sum_e (w_e/2)\cdot 4 = 2W(G)$, and the supremum over normalized states inherits the bound. In particular the optimum is finite for every finite weighted graph, which is what makes the supremum defining it well behaved.
-- source:
--   Elementary support estimate for Anshu-Gosset-Morenz TQC 2020 Theorem 1, https://doi.org/10.4230/LIPIcs.TQC.2020.7 ; bounds the campaign supremum so that every rounding lower bound is comparable to the total weight.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.optimum_le_two_mul_sum (G : QuantumMaxCutEnergy.Input) :
    QuantumMaxCutEnergy.optimum G ≤ 2 * ∑ e, (G.weights e : ℝ) := by sorry
