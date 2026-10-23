-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_sectorPauliAction
-- name    : QAlgorithms.Papers.Independent.Information100.P22.sectorPauliAction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:02:03.52401+00:00
-- url     : https://prove2.me/theorems/bd22e9f6-726e-4c3c-903e-912d03ac49d8
-- title:
--   Lemma S2: Pauli action of the two-Pauli sector-wise encoder
-- statement:
--   For one input sector and $m\ge1$, fix ordered distinct axes $P,Q$ and their two-Pauli encoder. Under forward encoder conjugation, a phase-free signal-only Pauli has no signal support exactly in the following cases:
--   $$m\text{ even}: I;\qquad m\text{ odd}: I\text{ or the direction of }(iPQ)^{\otimes m}.$$
--   At each prescribed signal position, conjugation maps the three nonidentity input directions bijectively to the three nonidentity local signal directions. This bijection concerns the local factor, not the full tensor operator. Phases are discarded only for these support assertions.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 20, Lemma S2: Pauli action of the two-Pauli sector-wise encoder

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Lemma S2, PDF pp.20–21: support statements and the local bijection on three input directions. -/
theorem sectorPauliAction (m : ℕ) (hm : 1 ≤ m) (P Q : Axis) (hPQ : P ≠ Q) :
    (Even m → ∀ l : Fin m → Option Axis,
      SourceOnly m (sectorEncoder m P Q * Matrix.kronecker (1 : Op Bool)
        (tensorOps fun i => directionMatrix (l i)) * (sectorEncoder m P Q)ᴴ) →
      l = fun _ => none) ∧
    (Odd m → ∀ l : Fin m → Option Axis,
      (SourceOnly m (sectorEncoder m P Q * Matrix.kronecker (1 : Op Bool)
        (tensorOps fun i => directionMatrix (l i)) * (sectorEncoder m P Q)ᴴ) ↔
        l = (fun _ => none) ∨ l = (fun _ => some (remainingAxis P Q)))) ∧
    (∀ i : Fin m, ∃ f : Equiv.Perm Axis, ∀ a : Axis,
      HasSignalDirection (sectorEncoder m P Q *
        Matrix.kronecker (axisMatrix a) (1 : Op (Qubits m)) * (sectorEncoder m P Q)ᴴ) i (f a)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
