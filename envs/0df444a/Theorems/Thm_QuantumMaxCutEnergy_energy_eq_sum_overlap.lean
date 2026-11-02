-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_energy_eq_sum_overlap
-- name    : QuantumMaxCutEnergy.energy_eq_sum_overlap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-02T04:16:53.854333+00:00
-- url     : https://prove2.me/theorems/9fd16027-bf97-4d55-97b5-a66a585d7a6c
-- title:
--   Energy as a sum of per-edge overlaps: $\\mathrm{energy}=\\sum_e w_e(1-\\mathrm{Re}\\langle\\psi,\\mathrm{SWAP}_e\\psi\\rangle)$
-- statement:
--   The energy functional of the Quantum Max-Cut model rewritten as a sum of per-edge overlap terms.
--
--   For a normalized wave function $\psi$ and edge weights $w$,
--   $$\mathrm{energy}(w,\psi) = \sum_{e} w_e\bigl(1 - \mathrm{Re}\,\langle \psi, \mathrm{SWAP}_e \psi\rangle\bigr),\qquad \langle \psi,\mathrm{SWAP}_e\psi\rangle = \sum_x \overline{\psi(x)}\,\psi(x\circ\sigma_e).$$
--   This is the bridge from the model's state-based energy (a sum over all basis amplitudes of squared differences) to the overlap form in which product-state and matching-state computations are done. Role: the aggregation identity under both rounding candidates of the level-2 analysis. **Formalization Note.** The identity is per edge: $\sum_x |\psi(x)-\psi(\sigma_e x)|^2 = 2(1-\mathrm{Re}\langle\psi,\mathrm{SWAP}_e\psi\rangle)$ at normalization $\sum|\psi|^2=1$; the file also proves the per-edge identity and the mixing scalars.
-- source:
--   Extracted from the level-2 Quantum Max-Cut analysis of Eunou Lee and Ojas Parekh, ICALP 2024, https://arxiv.org/abs/2401.03616

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.energy_eq_sum_overlap {n : ℕ} (w : QuantumMaxCutEnergy.Weights n) (ψ : QuantumMaxCutEnergy.Wave n)
    (hψ : QuantumMaxCutEnergy.squaredNorm ψ = 1) :
    QuantumMaxCutEnergy.energy w ψ = ∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ) *
      (1 - (∑ x, star (ψ x) * ψ (x ∘ Equiv.swap e.val.1 e.val.2)).re) := by sorry
