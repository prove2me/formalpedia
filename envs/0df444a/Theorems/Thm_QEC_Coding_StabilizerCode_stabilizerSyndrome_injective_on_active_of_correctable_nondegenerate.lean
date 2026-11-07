-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_stabilizerSyndrome_injective_on_active_of_correctable_nondegenerate
-- name    : QEC.Coding.StabilizerCode.stabilizerSyndrome_injective_on_active_of_correctable_nondegenerate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:58:11.849087+00:00
-- url     : https://prove2.me/theorems/70a63f90-6c31-4f35-9ade-02a4bfdb31ed
-- title:
--   Stabilizer Code: stabilizer Syndrome injective on active of correctable nondegenerate
-- statement:
--   If the active Pauli representatives contain no duplicates modulo stored sign,
--   the syndrome map is literally injective on active family indices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/SyndromeInjectivity.lean#L133-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/SyndromeInjectivity.lean#L133-L157

import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_Stabilizer_Degeneracy
import Definitions.Def_QEC_Coding_Stabilizer_SyndromeInjectivity
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.StabilizerCode.stabilizerSyndrome_injective_on_active_of_correctable_nondegenerate
    {κ : Type v} [Fintype κ] {α : Type w} [Fintype α]
    (Q : SourceValidBinary ι) (generators : κ → Binary ι)
    (hgenerated : {S | GeneratedStabilizer generators S} = Q.1.generatedGroup)
    (d t : Nat) (hd : SemanticStabilizerDistance Q d)
    (hNondegenerate : ¬ SemanticallyDegenerateAtDistance Q d)
    (E : α → Binary ι) (amp : α → Complex)
    (hcomplete : (binaryPauliKrausFamily E amp).Complete)
    (hcorrectable : ∃ recovery : Semantics.QuantumChannel
          (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι),
        Semantics.FiniteKrausCorrectable α
          (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι)
          Q.1.code (binaryPauliKrausFamily E amp) recovery)
    (hweight : ∀ i, amp i ≠ 0 → weight (E i) ≤ t)
    (hradius : 2 * t < d)
    (hNoDuplicates : ∀ i j, amp i ≠ 0 → amp j ≠ 0 →
      BinaryUpToSign (E i) (E j) → i = j) :
    Function.Injective (fun i : {i // amp i ≠ 0} =>
      stabilizerSyndrome generators (E i.1)) := by sorry
