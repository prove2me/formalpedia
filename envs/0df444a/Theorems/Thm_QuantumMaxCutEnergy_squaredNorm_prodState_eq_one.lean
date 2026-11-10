-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_squaredNorm_prodState_eq_one
-- name    : QuantumMaxCutEnergy.squaredNorm_prodState_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T14:18:23.190106+00:00
-- url     : https://prove2.me/theorems/f096d3d8-f5c6-4ee2-9e5a-71a80f825585
-- title:
--   Unit amplitudes give a normalised product state
-- statement:
--   **Unit amplitudes give a normalised state.**
--
--   If every amplitude pair is normalised, $|\alpha_i|^2+|\beta_i|^2=1$ for all $i$, then the product state has squared norm $\prod_i(|\alpha_i|^2+|\beta_i|^2)=1$: it is a legitimate quantum state.
--
--   This is what makes a candidate product state admissible in the supremum that defines `optimum`, the supremum of the energy over states of squared norm one. Without normalisation a candidate's energy would not be constrained by the optimum at all.
-- source:
--   Product states of the Quantum Max Cut Hamiltonian; normalisation of tensor products.

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEnergy_prodState

open Complex
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **Unit amplitudes give a normalised state.** -/
theorem squaredNorm_prodState_eq_one {n : ℕ} (α β : Fin n → ℂ)
    (h : ∀ i, Complex.normSq (α i) + Complex.normSq (β i) = 1) :
    squaredNorm (prodState α β) = 1 := by sorry

end QuantumMaxCutEnergy
