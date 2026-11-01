-- Prove2me | Theorems.Thm_ShendeQSD_Synthesis_demultiplex
-- name    : ShendeQSD.Synthesis.demultiplex
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:18:27.97552+00:00
-- url     : https://prove2.me/theorems/22faad35-b338-4315-83a3-d5f46c76531e
-- title:
--   Theorem 12: demultiplexing a multiplexor
-- statement:
--   Let $\iota$ be a finite data register and $U_0,U_1$ unitaries on it.
--
--   1. There are unitaries $V,W$ on $\iota$ and angles $\theta$ such that
--   $$
--   U_0\oplus U_1=(I\otimes V)\,\mathcal R_z(\theta)\,(I\otimes W),
--   $$
--   where $\mathcal R_z(\theta)$ is the multiplexed $R_z$ gate on the select qubit of $U_0\oplus U_1$ whose selects are the data qubits.
--   2. Conversely, for all unitaries $V,W$ and angles $\theta$, the operator $(I\otimes V)\mathcal R_z(\theta)(I\otimes W)$ is a multiplexor $U_0\oplus U_1$ of two unitaries.
--   3. Equivalently, as in the proof: there are unitaries $V,W$ and a unitary diagonal $D$ with $U_0\oplus U_1=(I\otimes V)(D\oplus D^\dagger)(I\otimes W)$.
--
--   This removes the multiplexing from a single-select multiplexor at the cost of one multiplexed rotation, which is what makes the Quantum Shannon Decomposition recurse on generic operators.
--
--   **Formalization Note** $I\otimes V$ is `1 ⊗ₖ V`; the multiplexed $R_z$ is `muxRot rz θ` with its target as the Bool factor.
--
--   Differences from the source:
--   - generalization: Theorem 12 for an (n−1)-qubit data bus → any finite data register ι; reason: specializes to ι = Qubits (n−1)
--   - reading: the circuit equivalence ≅ (p. 7) → both directions, every multiplexor decomposes and every right-hand side is a multiplexor of unitaries; reason: the paper's definition of ≅ for generic gates quantifies over both sides
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, Theorem 12 and its proof, pp. 13–14

import Definitions.Def_ShendeQSD_Synthesis_mux2
import Definitions.Def_ShendeQSD_Synthesis_muxRot
import Definitions.Def_ShendeQSD_Synthesis_rz

open scoped Kronecker

namespace ShendeQSD.Synthesis

/-- **Theorem 12: demultiplexing a multiplexor.**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
Theorem 12, pp. 13–14: a multiplexor `U₀ ⊕ U₁` (select = most significant qubit) equals, read left
to right, a generic gate `W` on the data qubits, a multiplexed `R_z` on the select qubit whose
selects are the data qubits, and a generic gate `V` on the data qubits. Proof (p. 13): "We want
unitary V, W and unitary diagonal D satisfying U = (I ⊗ V)(D ⊕ D†)(I ⊗ W)"; p. 14: "for D
diagonal, the matrix D ⊕ D† is in fact a multiplexed Rz gate acting on the most significant bit".

1. For all unitaries `U₀, U₁` on `ι` there are unitaries `V, W` and angles `θ` with
   `U₀ ⊕ U₁ = (I ⊗ V) · muxRot rz θ · (I ⊗ W)`.
2. Conversely, every such right-hand side is `U₀ ⊕ U₁` for some unitaries `U₀, U₁`.
3. The proof's form: there are unitaries `V, W` and a unitary diagonal `D = diag(d)` with
   `U₀ ⊕ U₁ = (I ⊗ V)(D ⊕ D†)(I ⊗ W)`.

**Formalization Note.** Generalization: any finite data register `ι` (the paper's is
`Qubits (n-1)`). `I ⊗ V` is `1 ⊗ₖ V`, the identity on the select qubit. `muxRot rz θ` has the
select qubit of `U₀ ⊕ U₁` as its target (the Bool factor) and `ι` as its selects. -/
theorem demultiplex {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (∀ U₀ ∈ Matrix.unitaryGroup ι ℂ, ∀ U₁ ∈ Matrix.unitaryGroup ι ℂ,
      ∃ V ∈ Matrix.unitaryGroup ι ℂ, ∃ W ∈ Matrix.unitaryGroup ι ℂ, ∃ θ : ι → ℝ,
        mux2 U₀ U₁ =
          ((1 : Matrix Bool Bool ℂ) ⊗ₖ V) * muxRot rz θ * ((1 : Matrix Bool Bool ℂ) ⊗ₖ W)) ∧
    (∀ V ∈ Matrix.unitaryGroup ι ℂ, ∀ W ∈ Matrix.unitaryGroup ι ℂ, ∀ θ : ι → ℝ,
      ∃ U₀ ∈ Matrix.unitaryGroup ι ℂ, ∃ U₁ ∈ Matrix.unitaryGroup ι ℂ,
        ((1 : Matrix Bool Bool ℂ) ⊗ₖ V) * muxRot rz θ * ((1 : Matrix Bool Bool ℂ) ⊗ₖ W) =
          mux2 U₀ U₁) ∧
    (∀ U₀ ∈ Matrix.unitaryGroup ι ℂ, ∀ U₁ ∈ Matrix.unitaryGroup ι ℂ,
      ∃ V ∈ Matrix.unitaryGroup ι ℂ, ∃ W ∈ Matrix.unitaryGroup ι ℂ, ∃ d : ι → ℂ,
        (∀ i, ‖d i‖ = 1) ∧
        mux2 U₀ U₁ = ((1 : Matrix Bool Bool ℂ) ⊗ₖ V) *
          mux2 (Matrix.diagonal d) (Matrix.diagonal (star d)) *
          ((1 : Matrix Bool Bool ℂ) ⊗ₖ W)) := by sorry

end ShendeQSD.Synthesis
