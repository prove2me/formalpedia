-- Prove2me | Theorems.Thm_ShendeQSD_Synthesis_two_qubit_diag_two_cnot
-- name    : ShendeQSD.Synthesis.two_qubit_diag_two_cnot
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:18:13.868422+00:00
-- url     : https://prove2.me/theorems/43e1bfa0-85e8-499c-ac3b-2e8e6014d0a3
-- title:
--   Theorem 14: a two-qubit operator is a diagonal followed by a two-CNOT circuit
-- statement:
--   1. Every unitary $U$ on two qubits can be written as
--   $$
--   U=(c\otimes e)\,\mathrm{CNOT}\,\big(R_y(\theta_1)\otimes R_y(\theta_2)\big)\,\mathrm{CNOT}\,(a\otimes b)\,\Delta,
--   $$
--   where $\Delta$ is a diagonal unitary, $a,b,c,e$ are one-qubit unitaries, $\theta_1,\theta_2$ are real, and both CNOTs have control the first (top) qubit.
--   2. Conversely, every product of this shape is unitary.
--
--   As a circuit: a diagonal gate, one-qubit gates, a CNOT, two $R_y$ rotations, a CNOT, one-qubit gates. The paper recites this result from [27] and uses it in Appendix A.2 to push the diagonal of each two-qubit operator into the next one, saving one CNOT per two-qubit operator but the last.
--
--   **Formalization Note** The first tensor factor is the top qubit and the control of `QAlgorithms.cnot`; $\Delta$ is `diagonal d` with $|d_p|=1$. $R_y$ is the paper's.
--
--   Differences from the source:
--   - reading: the circuit equivalence ≅ (p. 7) → both directions, every unitary decomposes and every product of the shape is unitary; reason: the paper's definition of ≅ for generic gates quantifies over both sides
--   - encoding: a generic diagonal gate Δ → diagonal matrix with entries of modulus 1; reason: a diagonal gate is a diagonal unitary
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, Appendix A.2, Theorem 14, p. 17 (cited from [27])

import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_ShendeQSD_Synthesis_ry

open scoped Kronecker

namespace ShendeQSD.Synthesis

open QAlgorithms

/-- **Theorem 14: decomposition of a two-qubit operator (cited from [27]).**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
Appendix A.2, Theorem 14, p. 17: a generic two-qubit operator equals, read left to right, a
diagonal gate `Δ` on both qubits, one-qubit gates `a` (top) and `b` (bottom), a CNOT with control
the top qubit, `R_y` gates on both qubits, a CNOT with control the top qubit, one-qubit gates `c`
(top) and `e` (bottom).

1. Every unitary `U` on two qubits is `(c ⊗ e) · CNOT · (R_y(θ₁) ⊗ R_y(θ₂)) · CNOT · (a ⊗ b) · Δ`
   with `a, b, c, e` one-qubit unitaries, `θ₁, θ₂` real and `Δ = diag(d)` a unitary diagonal.
2. Conversely, every such product is unitary.

**Formalization Note.** The two-qubit index is `Bool × Bool`, first factor = top (more
significant) qubit, which is also the control of `QAlgorithms.cnot`. `ry` is the paper's
convention (p. 5). The diagonal is a diagonal unitary (entries of modulus 1), not only a global
phase. -/
theorem two_qubit_diag_two_cnot :
    (∀ U ∈ Matrix.unitaryGroup (Bool × Bool) ℂ,
      ∃ d : Bool × Bool → ℂ, (∀ p, ‖d p‖ = 1) ∧
      ∃ a ∈ Matrix.unitaryGroup Bool ℂ, ∃ b ∈ Matrix.unitaryGroup Bool ℂ,
      ∃ c ∈ Matrix.unitaryGroup Bool ℂ, ∃ e ∈ Matrix.unitaryGroup Bool ℂ, ∃ θ₁ θ₂ : ℝ,
        U = (c ⊗ₖ e) * cnot * (ry θ₁ ⊗ₖ ry θ₂) * cnot * (a ⊗ₖ b) * Matrix.diagonal d) ∧
    (∀ d : Bool × Bool → ℂ, (∀ p, ‖d p‖ = 1) →
      ∀ a ∈ Matrix.unitaryGroup Bool ℂ, ∀ b ∈ Matrix.unitaryGroup Bool ℂ,
      ∀ c ∈ Matrix.unitaryGroup Bool ℂ, ∀ e ∈ Matrix.unitaryGroup Bool ℂ, ∀ θ₁ θ₂ : ℝ,
        (c ⊗ₖ e) * cnot * (ry θ₁ ⊗ₖ ry θ₂) * cnot * (a ⊗ₖ b) * Matrix.diagonal d ∈
          Matrix.unitaryGroup (Bool × Bool) ℂ) := by sorry

end ShendeQSD.Synthesis
