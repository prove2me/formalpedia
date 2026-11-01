-- Prove2me | Theorems.Thm_ShendeQSD_Synthesis_demux_single_rot
-- name    : ShendeQSD.Synthesis.demux_single_rot
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:18:37.487871+00:00
-- url     : https://prove2.me/theorems/0a2cfef2-5555-4787-a70b-2ae9bfe80d07
-- title:
--   Theorem 4: demultiplexing a singly-multiplexed $R_y$ or $R_z$
-- statement:
--   Let $R$ be $R_z$ or $R_y$, and consider two qubits: a data (target) qubit and a select qubit. Write $\mathrm{CNOT}$ for the CNOT with control the select qubit and target the data qubit.
--
--   1. For all angles $\theta_0,\theta_1$, the multiplexor $R(\theta_0)\oplus R(\theta_1)$ (apply $R(\theta_s)$ to the data qubit when the select carries $|s\rangle$) equals
--   $$
--   \mathrm{CNOT}\,\big(R(\tfrac{\theta_0-\theta_1}{2})\otimes I\big)\,\mathrm{CNOT}\,\big(R(\tfrac{\theta_0+\theta_1}{2})\otimes I\big),
--   $$
--   the circuit $R(\tfrac{\theta_0+\theta_1}{2})$, CNOT, $R(\tfrac{\theta_0-\theta_1}{2})$, CNOT.
--   2. Conversely, for all angles $a,b$ the circuit $\mathrm{CNOT}(R(a)\otimes I)\mathrm{CNOT}(R(b)\otimes I)$ is a singly-multiplexed $R$.
--
--   This is the base case of the recursive decomposition of multiplexed rotations into CNOTs and one-qubit rotations.
--
--   **Formalization Note** The two-qubit index is (data qubit, select qubit), the order of `muxRot`; the CNOT is `QAlgorithms.cnot` with its factors swapped. $R_y$ is the paper's.
--
--   Differences from the source:
--   - encoding: the select qubit drawn on top and the data qubit at the bottom → the data qubit as the first tensor factor; reason: the same operator up to the order of the tensor factors, the orientation used by every multiplexed rotation of the mission
--   - reading: the circuit equivalence ≅ (p. 7) → both directions, the explicit angles of p. 9 and the converse; reason: the paper's definition of ≅ for generic gates quantifies over both sides
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, §3.1 and Theorem 4, p. 9

import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_ShendeQSD_Synthesis_muxRot
import Definitions.Def_ShendeQSD_Synthesis_rz
import Definitions.Def_ShendeQSD_Synthesis_ry

open scoped Kronecker

namespace ShendeQSD.Synthesis

open QAlgorithms

/-- **Theorem 4: demultiplexing a singly-multiplexed `R_y` or `R_z`.**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
§3.1 and Theorem 4, p. 9: "we can implement the multiplexor R_z(θ0) ⊕ R_z(θ1) by the following
circuit": `R_z((θ0+θ1)/2)` on the data qubit, a CNOT from the select qubit, `R_z((θ0−θ1)/2)` on
the data qubit, a CNOT from the select qubit; "the exact same statement holds if we replace R_z by
R_y".

For `R = R_z` and `R = R_y`:
1. for all angles `θ₀ = θ false`, `θ₁ = θ true`,
   `muxRot R θ = CNOT · (R((θ₀−θ₁)/2) ⊗ I) · CNOT · (R((θ₀+θ₁)/2) ⊗ I)`;
2. conversely, every circuit `CNOT · (R(a) ⊗ I) · CNOT · (R(b) ⊗ I)` is a multiplexed `R`.

**Formalization Note.** Encoding: the index `Bool × Bool` is (data/target qubit, select qubit),
the order of `muxRot`; the paper's diagram draws the select on top. The CNOT has control the
select (second factor) and target the data qubit (first factor): `cnot.submatrix Prod.swap
Prod.swap`, with `QAlgorithms.cnot` (control first). The matrix product is the diagram read right
to left. -/
theorem demux_single_rot (R : ℝ → Matrix Bool Bool ℂ) (hR : R = rz ∨ R = ry) :
    (∀ θ : Bool → ℝ,
      muxRot R θ =
        cnot.submatrix Prod.swap Prod.swap *
          (R ((θ false - θ true) / 2) ⊗ₖ (1 : Matrix Bool Bool ℂ)) *
          cnot.submatrix Prod.swap Prod.swap *
          (R ((θ false + θ true) / 2) ⊗ₖ (1 : Matrix Bool Bool ℂ))) ∧
    (∀ a b : ℝ, ∃ θ : Bool → ℝ,
      cnot.submatrix Prod.swap Prod.swap * (R a ⊗ₖ (1 : Matrix Bool Bool ℂ)) *
          cnot.submatrix Prod.swap Prod.swap * (R b ⊗ₖ (1 : Matrix Bool Bool ℂ)) =
        muxRot R θ) := by sorry

end ShendeQSD.Synthesis
