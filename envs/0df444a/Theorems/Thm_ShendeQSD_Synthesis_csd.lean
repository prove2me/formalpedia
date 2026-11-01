-- Prove2me | Theorems.Thm_ShendeQSD_Synthesis_csd
-- name    : ShendeQSD.Synthesis.csd
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:18:43.520881+00:00
-- url     : https://prove2.me/theorems/c18d64af-2933-400b-88c5-06f0c655cf03
-- title:
--   Theorem 10: the Cosine–Sine decomposition
-- statement:
--   Let $\iota$ be a finite register and consider operators on one extra most significant qubit and $\iota$ (an arbitrary even dimension).
--
--   1. Every unitary $U$ can be written as
--   $$
--   U=\begin{pmatrix}A_1&\\&B_1\end{pmatrix}\begin{pmatrix}C&-S\\S&C\end{pmatrix}\begin{pmatrix}A_2&\\&B_2\end{pmatrix}
--   $$
--   with $A_1,A_2,B_1,B_2$ unitary on $\iota$ and $C,S$ real diagonal with $C^2+S^2=I$.
--   2. Conversely, every product of this shape is unitary.
--   3. Every middle factor $\begin{pmatrix}C&-S\\S&C\end{pmatrix}$ with $C^2+S^2=I$ is a multiplexed $R_y$ gate acting on the most significant qubit, with the low order qubits as selects.
--
--   So a generic operator is a multiplexor, a multiplexed $R_y$ and a multiplexor. This is the first step of the Quantum Shannon Decomposition.
--
--   **Formalization Note** The side factors are `mux2`, the middle factor `csMat`, the multiplexed rotation `muxRot ry`, with the paper's $R_y$.
--
--   Differences from the source:
--   - generalization: Theorem 10 for an n-qubit operator, the low order bits being an (n−1)-qubit register → any finite register ι, operators on Bool × ι; reason: specializes to ι = Qubits (n−1), and matches the even-dimensional statement of p. 12
--   - reading: the circuit equivalence ≅ (p. 7) → both directions, the decomposition of every unitary and the unitarity of every product of the shape; reason: the paper's definition of ≅ for generic gates quantifies over both sides
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, §5.1, p. 12 and Theorem 10, p. 13

import Definitions.Def_ShendeQSD_Synthesis_mux2
import Definitions.Def_ShendeQSD_Synthesis_csMat
import Definitions.Def_ShendeQSD_Synthesis_muxRot
import Definitions.Def_ShendeQSD_Synthesis_ry

namespace ShendeQSD.Synthesis

/-- **Theorem 10: the Cosine–Sine decomposition.**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
§5.1, p. 12 and Theorem 10, p. 13: "The CSD states that an even-dimensional unitary matrix
U ∈ C^{ℓ×ℓ} can be decomposed into smaller unitaries A1, A2, B1, B2 and real diagonal matrices
C, S such that C^2 + S^2 = I_{ℓ/2}", with U = (A1 ⊕ B1)(C −S ; S C)(A2 ⊕ B2); the central
factor "applies a different Ry gate to the most significant bit for each classical configuration
of the low order bits".

1. Every unitary `U` on `Bool × ι` is `mux2 A₁ B₁ * csMat C S * mux2 A₂ B₂` with `A₁, B₁, A₂, B₂`
   unitary on `ι` and `C, S` real with `C i ^ 2 + S i ^ 2 = 1`.
2. Conversely, every such product is unitary (the reverse direction of the circuit equivalence
   "≅", p. 7).
3. Every middle factor `csMat C S` with `C² + S² = I` is a multiplexed `R_y` gate on the most
   significant qubit, `muxRot ry θ` (the restatement as Theorem 10).

**Formalization Note.** Generalization: the data register is any finite type `ι`, so `Bool × ι`
is an arbitrary even dimension; the paper's `n`-qubit case is `ι = Qubits (n-1)`. The Bool factor
is the most significant qubit (the select of the side multiplexors and the target of the
multiplexed `R_y`). `ry` is the paper's convention (p. 5). -/
theorem csd {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (∀ U ∈ Matrix.unitaryGroup (Bool × ι) ℂ,
      ∃ A₁ ∈ Matrix.unitaryGroup ι ℂ, ∃ B₁ ∈ Matrix.unitaryGroup ι ℂ,
      ∃ A₂ ∈ Matrix.unitaryGroup ι ℂ, ∃ B₂ ∈ Matrix.unitaryGroup ι ℂ,
      ∃ C S : ι → ℝ, (∀ i, C i ^ 2 + S i ^ 2 = 1) ∧
        U = mux2 A₁ B₁ * csMat C S * mux2 A₂ B₂) ∧
    (∀ A₁ ∈ Matrix.unitaryGroup ι ℂ, ∀ B₁ ∈ Matrix.unitaryGroup ι ℂ,
      ∀ A₂ ∈ Matrix.unitaryGroup ι ℂ, ∀ B₂ ∈ Matrix.unitaryGroup ι ℂ,
      ∀ C S : ι → ℝ, (∀ i, C i ^ 2 + S i ^ 2 = 1) →
        mux2 A₁ B₁ * csMat C S * mux2 A₂ B₂ ∈ Matrix.unitaryGroup (Bool × ι) ℂ) ∧
    (∀ C S : ι → ℝ, (∀ i, C i ^ 2 + S i ^ 2 = 1) → ∃ θ : ι → ℝ, csMat C S = muxRot ry θ) := by sorry

end ShendeQSD.Synthesis
