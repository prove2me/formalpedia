-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P71_stabilizerPauli_bondOne
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P71.stabilizerPauli_bondOne
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:06:13.420859+00:00
-- url     : https://prove2.me/theorems/2443d6d8-5ef1-4eba-8bd4-7e734400f8c5
-- title:
--   Bond-one MPS and quadratic tableau construction for Pauli predictions
-- statement:
--   Let $\sigma$ be a pure $N$-qubit stabilizer projector and $O$ a Hermitian Pauli string with phase $\pm1$. For each region $A$, let $\sigma_A$ be its reduced state with normalized identity on the complement. The coefficient vector $o_A=\operatorname{Tr}(O\sigma_A)$ has the exact bond-one representation
--
--   $$o_A=\operatorname{Tr}(O\sigma)\prod_{i=1}^N t_i(\mathbf1_{i\in A}),\qquad t_i=(1,1)\ \text{if }O_i=I,\quad t_i=(0,1)\ \text{otherwise}.$$
--
--   This representation includes the identically zero vector, the identity Pauli, and empty or full regions. There are a uniform classical tableau program and an absolute constant $C$ such that, from the signed full stabilizer/destabilizer tableau and the Pauli string, it emits the scalar code and all $2N$ tensor entries within $C(N+1)^2$ elementary indexed word operations. The scalar is one of $0,\pm1$; machine cell values stay bounded by $C(N+1)^2$ throughout execution. No conversion of an arbitrary unsimplified generator list is counted as free preprocessing.
--
--   The result gives an explicitly stored MPS with linear output size and quadratic classical construction time; it counts neither the quantum experiment nor dense matrix construction.
-- source:
--   Classical Shadow Tomography with Locally Scrambled Quantum Dynamics, arXiv:2107.04817v4, PDF p. 20, Appendix C.2, Proposition I: bond-one MPS for reduced Pauli expectations

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P71

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Intakethird100.P71

attribute [local instance] Classical.propDecidable

local notation "Config" n:max d:max =>
  QAlgorithms.Papers.Independent.Information100.P21.Config (P := Fin n) (fun _ => d)

local notation "Op" n:max d:max =>
  QAlgorithms.Papers.Independent.Information100.P21.Op (Config n d)

attribute [local instance] QAlgorithms.Papers.Independent.Intakethird100.P71.matrixContinuousENorm

local notation "Unitary" n:max d:max => Matrix.unitaryGroup (Config n d) ℂ

local notation "Local" n:max d:max => Fin n → Matrix.unitaryGroup (Fin d) ℂ

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF pp.20–21 Proposition I, Eqs.(C2)–(C7): exact bond-one factors for all
pure stabilizer snapshots, including a zero coefficient vector. The uniform
classical RAM program is quantified before N and the tableau. Its output is
one signed scalar plus 2N tensor entries; quadratic time includes scalar
computation on the full signed dual simulation tableau, and tensor writes.
The RAM uses the frozen elementary indexed/bit-operation semantics. -/
theorem stabilizerPauli_bondOne :
    (∀ (n : ℕ) (T : QAlgorithms.Stabilizer.Tableau n),
      QAlgorithms.Stabilizer.IsValidTableau T →
      ∀ O : QAlgorithms.Stabilizer.PauliString n, (O.phase = 0 ∨ O.phase = 2) →
        ∀ A : Finset (Fin n),
          (O.toMatrix * reducedSnapshot A (QAlgorithms.Stabilizer.tableauProjector T)).trace =
            (O.toMatrix * QAlgorithms.Stabilizer.tableauProjector T).trace *
              ∏ i, pauliFactor O i (decide (i ∈ A))) ∧
    ∃ (P : QAlgorithms.ExpanderCodes.DecoderImplementation) (C : ℕ), 0 < C ∧
      ∀ (n : ℕ) (T D : QAlgorithms.Stabilizer.Tableau n), DualTableau T D →
        ∀ O : QAlgorithms.Stabilizer.PauliString n, (O.phase = 0 ∨ O.phase = 2) →
          ∃ t : ℕ, t ≤ C*(n+1)^2 ∧
            (QAlgorithms.ExpanderCodes.decoderExecution P (tableauInput T D O) t).halted = some true ∧
            (QAlgorithms.ExpanderCodes.decoderExecution P (tableauInput T D O) t).output = tableauRecord T O ∧
            (∀ u ≤ t, ∀ i : ℕ,
              (QAlgorithms.ExpanderCodes.decoderExecution P (tableauInput T D O) u).memory i ≤ C*(n+1)^2) ∧
            (O.toMatrix * QAlgorithms.Stabilizer.tableauProjector T).trace ∈ ({0,1,-1} : Set ℂ) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P71

end
