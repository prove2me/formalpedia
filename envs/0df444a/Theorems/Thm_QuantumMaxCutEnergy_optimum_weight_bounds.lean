-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_optimum_weight_bounds
-- name    : QuantumMaxCutEnergy.optimum_weight_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-31T23:50:14.119485+00:00
-- url     : https://prove2.me/theorems/21c8fe15-d002-4fa5-a6d7-8f2175cf9ff6
-- title:
--   Quantum Max-Cut optimum bounds from total edge weight
-- statement:
--   Let $G$ be a finite graph with nonnegative rational edge weights, and write $W=\sum_{i<j}w_{ij}$. In the convention $H_G=\sum_{i<j}w_{ij}(I-\mathrm{SWAP}_{ij})$, its optimal energy satisfies
--
--   $$\frac W2\le\mathrm{OPT}(G)\le2W.$$
--
--   The optimum ranges over all normalized quantum states. Both inequalities include empty graphs and zero weights. These analytic bounds justify the numerical value $W/2$ as a $1/4$ lower estimate. This supporting theorem does not assert a polynomial-time implementation; that remains a separate obligation in the campaign's algorithmic theorem.
-- source:
--   Elementary trace/averaging and edgewise energy bounds, proved directly in this formalization. Corresponds to the maximally mixed 1/4 baseline discussed by Gharibian and Parekh (2019), Introduction1.2, https://arxiv.org/html/1909.08846 , with Hamiltonian rescaled by1/2 to the shared convention.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
open scoped BigOperators

theorem QuantumMaxCutEnergy.optimum_weight_bounds (G : QuantumMaxCutEnergy.Input) :
    (∑ e, (G.weights e : ℝ)) / 2 ≤ QuantumMaxCutEnergy.optimum G ∧
      QuantumMaxCutEnergy.optimum G ≤ 2 * (∑ e, (G.weights e : ℝ)) := by sorry
