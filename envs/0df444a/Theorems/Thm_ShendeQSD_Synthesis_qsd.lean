-- Prove2me | Theorems.Thm_ShendeQSD_Synthesis_qsd
-- name    : ShendeQSD.Synthesis.qsd
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:18:30.767291+00:00
-- url     : https://prove2.me/theorems/13d223e9-3c1b-43f0-9dc5-067048fa78ea
-- title:
--   Theorem 13: the Quantum Shannon Decomposition
-- statement:
--   Let $\iota$ be a finite register (the bus) and consider operators on one top qubit and the bus.
--
--   1. Every unitary $U$ factors as
--   $$
--   U=(I\otimes V_4)\,\mathcal R_z(\gamma)\,(I\otimes V_3)\,\mathcal R_y(\beta)\,(I\otimes V_2)\,\mathcal R_z(\alpha)\,(I\otimes V_1),
--   $$
--   where $V_1,\dots,V_4$ are unitaries on the bus and $\mathcal R_z,\mathcal R_y$ are multiplexed rotations with target the top qubit and selects the bus.
--   2. Conversely, every product of this shape is unitary.
--
--   Read as a circuit (right to left), an arbitrary operator is four generic operators on one fewer qubit separated by three multiplexed rotations. Applied recursively, this is the synthesis algorithm whose CNOT count the mission bounds.
--
--   **Formalization Note** The multiplexed rotations are `muxRot rz` and `muxRot ry` (paper's $R_y$), $I\otimes V$ is `1 ⊗ₖ V`.
--
--   Differences from the source:
--   - generalization: Theorem 13 for an n-qubit operator with an (n−1)-qubit bus → any finite bus ι; reason: specializes to ι = Qubits (n−1)
--   - reading: the circuit equivalence ≅ (p. 7) → both directions, every unitary factors and every product of the shape is unitary; reason: the paper's definition of ≅ for generic gates quantifies over both sides
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, Theorem 13, p. 14

import Definitions.Def_ShendeQSD_Synthesis_muxRot
import Definitions.Def_ShendeQSD_Synthesis_rz
import Definitions.Def_ShendeQSD_Synthesis_ry

open scoped Kronecker

namespace ShendeQSD.Synthesis

/-- **Theorem 13: the Quantum Shannon Decomposition.**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
Theorem 13, p. 14: a generic operator on the top qubit and a bus equals, read left to right, a
generic operator `V₁` on the bus, a multiplexed `R_z` on the top qubit (selects = the bus), a
generic `V₂`, a multiplexed `R_y`, a generic `V₃`, a multiplexed `R_z`, a generic `V₄`. "Hence an
arbitrary n-qubit operator can be implemented by a circuit containing three multiplexed rotations
and four generic (n − 1)-qubit operators".

1. Every unitary `U` on `Bool × ι` is
   `(I ⊗ V₄) R_z(γ) (I ⊗ V₃) R_y(β) (I ⊗ V₂) R_z(α) (I ⊗ V₁)` (multiplexed rotations) with
   `V₁, …, V₄` unitary on `ι`.
2. Conversely, every such product is unitary.

**Formalization Note.** Generalization: any finite bus `ι` (the paper's is `Qubits (n-1)`). The
Bool factor is the top (most significant) qubit, the target of the three multiplexed rotations.
The matrix product is the diagram read right to left (Figure 1, p. 7). `ry` is the paper's
convention (p. 5). -/
theorem qsd {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (∀ U ∈ Matrix.unitaryGroup (Bool × ι) ℂ,
      ∃ V₁ ∈ Matrix.unitaryGroup ι ℂ, ∃ V₂ ∈ Matrix.unitaryGroup ι ℂ,
      ∃ V₃ ∈ Matrix.unitaryGroup ι ℂ, ∃ V₄ ∈ Matrix.unitaryGroup ι ℂ,
      ∃ α β γ : ι → ℝ,
        U = ((1 : Matrix Bool Bool ℂ) ⊗ₖ V₄) * muxRot rz γ * ((1 : Matrix Bool Bool ℂ) ⊗ₖ V₃) *
          muxRot ry β * ((1 : Matrix Bool Bool ℂ) ⊗ₖ V₂) * muxRot rz α *
          ((1 : Matrix Bool Bool ℂ) ⊗ₖ V₁)) ∧
    (∀ V₁ ∈ Matrix.unitaryGroup ι ℂ, ∀ V₂ ∈ Matrix.unitaryGroup ι ℂ,
      ∀ V₃ ∈ Matrix.unitaryGroup ι ℂ, ∀ V₄ ∈ Matrix.unitaryGroup ι ℂ,
      ∀ α β γ : ι → ℝ,
        ((1 : Matrix Bool Bool ℂ) ⊗ₖ V₄) * muxRot rz γ * ((1 : Matrix Bool Bool ℂ) ⊗ₖ V₃) *
          muxRot ry β * ((1 : Matrix Bool Bool ℂ) ⊗ₖ V₂) * muxRot rz α *
          ((1 : Matrix Bool Bool ℂ) ⊗ₖ V₁) ∈ Matrix.unitaryGroup (Bool × ι) ℂ) := by sorry

end ShendeQSD.Synthesis
