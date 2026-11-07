-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_stabilizerSyndrome_injectiveUpToSign_of_correctable_nondegenerate
-- name    : QEC.Coding.StabilizerCode.stabilizerSyndrome_injectiveUpToSign_of_correctable_nondegenerate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:13:20.242089+00:00
-- url     : https://prove2.me/theorems/5b5e7277-63f3-4a85-a7bf-aed9eb7620f2
-- title:
--   Stabilizer Code: stabilizer Syndrome injective Up To Sign of correctable nondegenerate
-- statement:
--   For a source-valid binary stabilizer code with finite semantic distance, a
--   complete correctable finite binary-Pauli Kraus family supported in a radius
--   strictly below half the distance has generator-indexed syndromes that are
--   injective up to stored binary sign on its nonzero-amplitude support.
--
--   This realizes the bounded nondegenerate syndrome distinction of
--   [Gott97, Ch. 2, distance paragraph; Ch. 3, stabilizer error-set criterion,
--   stabilizer distance and degeneracy paragraph, and error syndrome].
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/SyndromeInjectivity.lean#L73-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/SyndromeInjectivity.lean#L73-L127

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

theorem QEC.Coding.StabilizerCode.stabilizerSyndrome_injectiveUpToSign_of_correctable_nondegenerate
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
    (hradius : 2 * t < d) :
    ∀ i j, amp i ≠ 0 → amp j ≠ 0 →
      stabilizerSyndrome generators (E i) = stabilizerSyndrome generators (E j) →
      BinaryUpToSign (E i) (E j) := by sorry
