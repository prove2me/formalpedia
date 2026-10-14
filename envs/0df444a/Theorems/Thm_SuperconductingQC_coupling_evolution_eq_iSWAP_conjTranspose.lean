-- Prove2me | Theorems.Thm_SuperconductingQC_coupling_evolution_eq_iSWAP_conjTranspose
-- name    : SuperconductingQC.coupling_evolution_eq_iSWAP_conjTranspose
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T01:24:02.153+00:00
-- url     : https://prove2.me/theorems/c0c0b803-ff49-4c1c-bbe9-8598c13712a1
-- title:
--   Coherent exchange under the transmon coupling Hamiltonian realises iSWAP
-- statement:
--   Let $\hbar\neq0$ and $J\neq0$ be real numbers and let
--   $$H=\frac{\hbar J}{2}\left(\sigma^x_1\sigma^x_2+\sigma^y_1\sigma^y_2\right)$$
--   be the Hamiltonian of two capacitively coupled transmons. Then evolving for time $t=\pi/(2J)$ gives
--   $$\exp\left(-\frac{i t}{\hbar}H\right)\Big|_{t=\pi/(2J)}=\mathrm{iSWAP}^{\dagger},$$
--   the conjugate transpose of the iSWAP gate, i.e. the gate $|00\rangle\mapsto|00\rangle$, $|01\rangle\mapsto -i|10\rangle$, $|10\rangle\mapsto -i|01\rangle$, $|11\rangle\mapsto|11\rangle$.
--
--   This makes precise the statement that two-qubit gates of iSWAP type are produced by coherent exchange in the coupled-transmon Hamiltonian. Since iSWAP† and iSWAP differ by single-qubit gates ($\mathrm{iSWAP}^\dagger=(Z\otimes Z)\,\mathrm{iSWAP}$), it links the physical Hamiltonian to the gate set of the goal theorem.
--
--   **Formalization Note** $J$ may be negative (then $t<0$); the identity holds for every nonzero $J$.
-- source:
--   Wikipedia, "Superconducting quantum computing" (PDF snapshot supplied by the mission author, retrieved 2026-10-13), https://en.wikipedia.org/wiki/Superconducting_quantum_computing; section 'Quantum gates' (iSWAP via coherent exchange) and section 'Transmon' (two-transmon Hamiltonian H = (ħJ/2)(σ1x σ2x + σ1y σ2y))

import Mathlib
import Definitions.Def_SuperconductingQC_Gates

open scoped Matrix Kronecker

namespace SuperconductingQC

theorem coupling_evolution_eq_iSWAP_conjTranspose (hbar J : ℝ) (hhbar : hbar ≠ 0)
    (hJ : J ≠ 0) :
    timeEvolution hbar (Real.pi / (2 * J)) (couplingHamiltonian hbar J) = iSWAPᴴ := by
  sorry

end SuperconductingQC
