-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_forest_cut_energy_lower
-- name    : QuantumMaxCutEnergy.forest_cut_energy_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T01:07:53.165221+00:00
-- url     : https://prove2.me/theorems/02db38fa-37c1-4471-90fa-b5d3fb778b95
-- title:
--   A forest yields a feasible Quantum Max-Cut energy bound
-- statement:
--   Every forest $F$ in a graph with nonnegative rational edge weights has a Boolean assignment cutting all its edges. Its normalized computational-basis vector satisfies
--
--   $$\sum_{e\in F}w_e\le\langle b,H_G b\rangle.$$
--
--   The Hamiltonian includes all graph edges. This verifies the mathematical feasibility assertion in published Eq. (26); a polynomial-time implementation of the coloring is a separate obligation. Empty forests and zero weights are included.
-- source:
--   Anshu, Gosset, and Morenz, TQC 2020, Eq. (26), p. 7:10, in the proof of Theorem 3. https://doi.org/10.4230/LIPIcs.TQC.2020.7 . The theorem gives a Boolean assignment, cuts all forest edges, normalizes its basis vector, and bounds its QMC energy. It does not supply a runtime certificate.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.forest_cut_energy_lower {n : ℕ} (F : Finset (QuantumMaxCutEnergy.Edge n)) (w : QuantumMaxCutEnergy.Weights n)
    (hF : (⨆ e ∈ F, SimpleGraph.edge e.val.1 e.val.2).IsAcyclic) :
    ∃ b : QuantumMaxCutEnergy.Basis n, (∀ e ∈ F, b e.val.1 ≠ b e.val.2) ∧
      QuantumMaxCutEnergy.squaredNorm (fun x => if x = b then 1 else 0) = 1 ∧
      (∑ e ∈ F, (w e : ℝ)) ≤ QuantumMaxCutEnergy.energy w (fun x => if x = b then 1 else 0) := by sorry
