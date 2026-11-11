-- Prove2me | Theorems.Thm_PSPACEOracleSynth_Main_lemma_2_7
-- name    : PSPACEOracleSynth.Main.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:16.6295+00:00
-- url     : https://prove2.me/theorems/7659014d-0279-4370-aa3d-e64b00cf69d9
-- title:
--   Lemma 2.7 — close isometries, and from an error on the zero-ancilla subspace to an extension or dilation at distance $3\varepsilon$
-- statement:
--   1. Let $Y_1,Y_2:K\to H$ be isometries with $\|Y_1-Y_2\|\le\varepsilon<1$. There is a unitary $W$ on $H$ with
--   $$WY_1=Y_2,\qquad\|W-I\|\le2\varepsilon+\varepsilon^2.$$
--   2. Consequently, if a unitary $C$ on $n+a$ qubits implements a unitary $U$ on $n$ qubits on the zero-ancilla subspace with error $\varepsilon<1$, i.e. $\|C\iota_a-\iota_aU\|\le\varepsilon$, then $U$ has an extension $\tilde U$ with $\|C-\tilde U\|\le3\varepsilon$.
--   3. The same holds for a dilation with garbage state $|g\rangle$ if $\|C\iota_a-U\otimes|g\rangle\|\le\varepsilon$: there is a dilation $\tilde U$ of $U$ with garbage state $|g\rangle$ and $\|C-\tilde U\|\le3\varepsilon$.
--
--   This converts the error bounds of the constructions, which hold on the zero-ancilla subspace, into the whole-space bounds required by the classes of Definition 2.3.
--
--   **Formalization Note.** In item 1, $K$ and $H$ are arbitrary complex Hilbert spaces and $Y_1,Y_2$ bounded linear maps with $Y_i^\dagger Y_i=I$. In items 2–3, $C$ is any unitary $2^{n+a}\times2^{n+a}$ matrix, the data are on the first $n$ wires and the ancillas on the last $a$, and $|g\rangle$ is a unit vector; norms are operator norms.
--
--   Differences from the source:
--   - generalization: a unitary circuit C (items 2–3) → any unitary matrix C on n + a qubits; reason: the matrix of a unitary circuit is unitary, so the circuit statement is the special case
--   - reading: isometries Y_1, Y_2 : K → H (spaces unspecified) → bounded linear maps between arbitrary complex Hilbert spaces with Y†Y = I; reason: covers the finite-dimensional spaces of the paper's uses
--   - encoding: garbage state |g⟩ → a vector g with Σ|g(x)|² = 1; reason: a state is a unit vector
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), §2.4, Lemma 2.7, p. 13

import Mathlib
import Definitions.Def_KTUnitary_Synth_IsExtension
import Definitions.Def_KTUnitary_Synth_opNorm
import Definitions.Def_PSPACEOracleSynth_Main_Dilation

open QAlgorithms.Complexity KTUnitary.Synth

namespace PSPACEOracleSynth.Main

/-- **Lemma 2.7**, Sichen Wang, *Unitary Synthesis with a PSPACE Oracle*, STOC 2027 submission
#1740, p. 13.

1. Let `Y₁, Y₂ : K → H` be isometries with `‖Y₁ − Y₂‖ ≤ ε < 1`. There is a unitary `W` on `H`
   with `W Y₁ = Y₂` and `‖W − I‖ ≤ 2ε + ε²`.
2. If a unitary `C` on `N = n + a` qubits implements a unitary `U` on `n` qubits on the
   zero-ancilla subspace with error `ε < 1` (`‖C ι_a − ι_a U‖ ≤ ε`), then `U` has an extension `Ũ`
   with `‖C − Ũ‖ ≤ 3ε`.
3. The same holds for a dilation with garbage state `|g⟩` (a unit vector) if
   `‖C ι_a − U ⊗ |g⟩‖ ≤ ε`: there is a dilation `Ũ` of `U` with garbage state `|g⟩` and
   `‖C − Ũ‖ ≤ 3ε`. -/
theorem lemma_2_7 :
    (∀ {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
        (Y₁ Y₂ : K →L[ℂ] H) (ε : ℝ),
        ContinuousLinearMap.adjoint Y₁ ∘L Y₁ = ContinuousLinearMap.id ℂ K →
        ContinuousLinearMap.adjoint Y₂ ∘L Y₂ = ContinuousLinearMap.id ℂ K →
        ‖Y₁ - Y₂‖ ≤ ε → ε < 1 →
        ∃ W ∈ unitary (H →L[ℂ] H), W ∘L Y₁ = Y₂ ∧ ‖W - 1‖ ≤ 2 * ε + ε ^ 2) ∧
    (∀ {n N : ℕ} (h : n ≤ N) (C : Matrix (Bits N) (Bits N) ℂ) (U : Matrix (Bits n) (Bits n) ℂ)
        (ε : ℝ), C ∈ Matrix.unitaryGroup (Bits N) ℂ → U ∈ Matrix.unitaryGroup (Bits n) ℂ →
        opNormR (C * ancMat h - ancMat h * U) ≤ ε → ε < 1 →
        ∃ Ub, IsExtension h U Ub ∧ opNorm (C - Ub) ≤ 3 * ε) ∧
    (∀ {n N : ℕ} (h : n ≤ N) (C : Matrix (Bits N) (Bits N) ℂ) (U : Matrix (Bits n) (Bits n) ℂ)
        (g : Bits (N - n) → ℂ) (ε : ℝ), C ∈ Matrix.unitaryGroup (Bits N) ℂ →
        U ∈ Matrix.unitaryGroup (Bits n) ℂ → ∑ x, ‖g x‖ ^ 2 = 1 →
        opNormR (C * ancMat h - dilMat h U g) ≤ ε → ε < 1 →
        ∃ Ub, IsDilationWith h U Ub g ∧ opNorm (C - Ub) ≤ 3 * ε) := by sorry

end PSPACEOracleSynth.Main
