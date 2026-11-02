-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_interactionDependent_examples
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.interactionDependent_examples
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:11:55.007696+00:00
-- url     : https://prove2.me/theorems/7cc535c9-2574-47a9-bdd2-41fe3d454b0f
-- title:
--   Ising and exchange interactions give different gate orderings
-- statement:
--   Use instantaneous free local controls and the ideal interaction-cost model on exactly two qubits. Write $H_I=X\otimes X$ for unit-strength Ising interaction and $H_E=X\otimes X+Y\otimes Y+Z\otimes Z$ for unit-strength exchange interaction, where $X,Y,Z$ are the Pauli spin matrices. With CNOT, DCNOT and SWAP acting as $|i,j\rangle\mapsto|i,i\oplus j\rangle$, $|j,i\oplus j\rangle$ and $|j,i\rangle$, respectively,
--
--   $$\begin{aligned}C_{H_I}(\mathrm{CNOT})&=\pi/4<C_{H_I}(\mathrm{DCNOT})=\pi/2<C_{H_I}(\mathrm{SWAP})=3\pi/4,\\C_{H_E}(\mathrm{SWAP})&=\pi/4<C_{H_E}(\mathrm{DCNOT})=\pi/2.\end{aligned}$$
--
--   These examples show that the ordering by cost can change with the interaction. Hamiltonian strength one is allowed even though a gate-content coordinate is bounded by $\pi/4$.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 7, III.E: interaction-dependent ordering examples

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF p.7, III.E: unit-strength Ising and exchange interactions give different gate
orderings. Strength 1 is not constrained by the gate-chamber bound pi/4. -/
theorem interactionDependent_examples :
    interactionCost (canonicalPauliInteraction ![1, 0, 0]) cnot = ENNReal.ofReal (Real.pi / 4) ∧
    interactionCost (canonicalPauliInteraction ![1, 0, 0]) dcnot = ENNReal.ofReal (Real.pi / 2) ∧
    interactionCost (canonicalPauliInteraction ![1, 0, 0]) swapGate =
      ENNReal.ofReal (3 * Real.pi / 4) ∧
    interactionCost (canonicalPauliInteraction ![1, 0, 0]) cnot <
      interactionCost (canonicalPauliInteraction ![1, 0, 0]) dcnot ∧
    interactionCost (canonicalPauliInteraction ![1, 0, 0]) dcnot <
      interactionCost (canonicalPauliInteraction ![1, 0, 0]) swapGate ∧
    interactionCost (canonicalPauliInteraction ![1, 1, 1]) swapGate = ENNReal.ofReal (Real.pi / 4) ∧
    interactionCost (canonicalPauliInteraction ![1, 1, 1]) dcnot = ENNReal.ofReal (Real.pi / 2) ∧
    interactionCost (canonicalPauliInteraction ![1, 1, 1]) swapGate <
      interactionCost (canonicalPauliInteraction ![1, 1, 1]) dcnot := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
