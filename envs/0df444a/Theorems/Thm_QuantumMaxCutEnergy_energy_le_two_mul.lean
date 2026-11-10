-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_energy_le_two_mul
-- name    : QuantumMaxCutEnergy.energy_le_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T14:49:31.388238+00:00
-- url     : https://prove2.me/theorems/72592357-a36d-404d-8baf-6823290cccd4
-- title:
--   The energy of any state is at most twice the total weight times its norm
-- statement:
--   **The energy of a state is bounded by its norm.**
--
--   For any wave function $\psi$ on $n$ qubits and any weights $w$,
--   $$\mathrm{energy}_w(\psi)=\sum_{e}\frac{w_e}{2}\sum_{x}\big|\psi(x)-\psi(x\circ\mathrm{swap}_e)\big|^2 \;\le\; 2\Big(\sum_e w_e\Big)\|\psi\|^2 .$$
--
--   The chain is: $|a-b|^2\le 2|a|^2+2|b|^2$ pointwise; summing over $x$ and using that $x\mapsto x\circ\mathrm{swap}_e$ is a bijection of $\{0,1\}^n$ gives $\sum_x|\psi(x)-\psi(x\circ\mathrm{swap}_e)|^2\le 4\|\psi\|^2$; then sum over edges.
--
--   For normalised $\psi$ this reads $\mathrm{energy}_w(\psi)\le 2\sum_e w_e$ **uniformly**. That uniform bound is what makes the set of energies bounded above, hence the supremum `optimum` well behaved — `le_csSup` requires it. Without it one cannot conclude that a candidate state's energy is below the optimum, which is the soundness half of every approximation-ratio argument.
-- source:
--   Quantum Max Cut Hamiltonian energy bound; establishes BddAbove for the supremum defining QuantumMaxCutEnergy.optimum.

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEnergy_prodState

open Complex
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **Energy bound.** `energy w ψ ≤ 2 (Σ_e w e) ‖ψ‖²`. -/
theorem energy_le_two_mul (n : ℕ) (w : Weights n) (ψ : Wave n) :
    energy w ψ ≤ 2 * (∑ e, (w e : ℝ)) * squaredNorm ψ := by sorry

end QuantumMaxCutEnergy
