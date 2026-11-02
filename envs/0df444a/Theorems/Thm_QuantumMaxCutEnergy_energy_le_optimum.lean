-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_energy_le_optimum
-- name    : QuantumMaxCutEnergy.energy_le_optimum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T16:56:36.800201+00:00
-- url     : https://prove2.me/theorems/1df6cc9d-5a2f-4b1c-8f1b-7562fdc2dd8c
-- title:
--   A normalized state's energy never exceeds the Quantum Max-Cut optimum
-- statement:
--   For every number of qubits $n$, every assignment $w$ of nonnegative rational weights to the pairs of qubits, and every state vector $\psi$ with $\sum_x |\psi(x)|^2 = 1$, the Quantum Max-Cut energy
--
--   $$\sum_{e} \frac{w_e}{2}\sum_x \bigl|\psi(x)-\psi(x\circ\sigma_e)\bigr|^2$$
--
--   of $\psi$ is at most the optimum, defined as the supremum of that energy over all normalized state vectors.
--
--   This is the glue step of every constructive lower bound on the optimum: exhibiting one normalized state whose energy is at least $c$ certifies $\mathrm{OPT}\ge c$. It is the only way a rounding argument meets the campaign's supremum definition.
-- source:
--   Order-theoretic support lemma for Anshu-Gosset-Morenz TQC 2020 Theorem 1 (product-state rounding for Quantum Max-Cut), https://doi.org/10.4230/LIPIcs.TQC.2020.7 , used to convert an exhibited product state into a lower bound for the optimum.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.energy_le_optimum
    {n : ℕ} (w : QuantumMaxCutEnergy.Weights n) (ψ : QuantumMaxCutEnergy.Wave n)
    (hψ : QuantumMaxCutEnergy.squaredNorm ψ = 1) :
    QuantumMaxCutEnergy.energy w ψ ≤ QuantumMaxCutEnergy.optimum ⟨n, w⟩ := by sorry
