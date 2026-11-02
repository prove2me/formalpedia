-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_unit_bloch_assignment_energy_lower_bound
-- name    : QuantumMaxCutEnergy.unit_bloch_assignment_energy_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T15:59:30.128994+00:00
-- url     : https://prove2.me/theorems/754434fa-3739-405f-85bc-4c20979b311c
-- title:
--   Unit Bloch vectors give a feasible Quantum Max-Cut energy
-- statement:
--   For every graph $G$ with nonnegative rational edge weights and every assignment of unit vectors $r_i\in\mathbb R^3$,
--
--   $$\sum_{\{i,j\}}\frac{w_{ij}}2(1-r_i\cdot r_j)\le\mathrm{OPT}(G).$$
--
--   Thus the Bloch-vector product objective is a valid lower bound on Quantum Max-Cut energy.
-- source:
--   Gharibian and Parekh, APPROX/RANDOM2019, Bloch-vector product-state representation, https://doi.org/10.4230/LIPIcs.APPROX-RANDOM.2019.31 ; Anshu, Gosset and Morenz,TQC2020,Eq.(6), https://doi.org/10.4230/LIPIcs.TQC.2020.7 .

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

open scoped BigOperators

theorem QuantumMaxCutEnergy.unit_bloch_assignment_energy_lower_bound (G : QuantumMaxCutEnergy.Input) (r : Fin G.n → Fin 3 → ℝ)
    (hr : ∀ i, (∑ a : Fin 3, (r i a) ^ 2) = 1) :
    (∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) *
      (1 - ∑ a : Fin 3, r e.val.1 a * r e.val.2 a) / 2) ≤ QuantumMaxCutEnergy.optimum G := by sorry
