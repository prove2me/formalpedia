-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_squaredNorm_prodState
-- name    : QuantumMaxCutEnergy.squaredNorm_prodState
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T14:18:18.159441+00:00
-- url     : https://prove2.me/theorems/2a0b7e2b-8e44-4276-8dae-69ffd58b083f
-- title:
--   The squared norm of a product state is the product of the per-qubit norms
-- statement:
--   **A product state is normalised exactly when its factors are.**
--
--   For amplitude families $\alpha,\beta : \{1,\dots,n\}\to\mathbb C$,
--   $$\|\psi\|^2=\sum_{x\in\{0,1\}^n}\prod_i\left|\begin{cases}\beta_i & x_i=1\\ \alpha_i & x_i=0\end{cases}\right|^2=\prod_{i=1}^{n}\big(|\alpha_i|^2+|\beta_i|^2\big).$$
-- source:
--   Product states of the Quantum Max Cut Hamiltonian; normalisation of tensor products.

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEnergy_prodState

open Complex
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **The squared norm of a product state is the product of the per-qubit norms.** -/
theorem squaredNorm_prodState {n : ℕ} (α β : Fin n → ℂ) :
    squaredNorm (prodState α β)
      = ∏ i, (Complex.normSq (α i) + Complex.normSq (β i)) := by sorry

end QuantumMaxCutEnergy
