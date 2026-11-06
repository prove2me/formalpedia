-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_exists_finiteKrausCorrectable_iff_pairProductCriterion_on_support
-- name    : QEC.Coding.StabilizerCode.exists_finiteKrausCorrectable_iff_pairProductCriterion_on_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:45:41.688833+00:00
-- url     : https://prove2.me/theorems/806872e2-94d5-4428-9e15-4dd40f7d5749
-- title:
--   Stabilizer Code: exists finite Kraus Correctable iff pair Product Criterion on support
-- statement:
--   A complete finite Kraus family of scaled binary Pauli operators is correctable
--   by a CPTP recovery exactly when every relative Pauli on the nonzero-amplitude
--   support is stabilizer-degenerate or outside the binary normalizer.
--
--   This is the source-exact realization of [Gott97, Ch. 2, Eq. (2.5); Ch. 3,
--   stabilizer error-set criterion] and [KL96, Theorem 2.1].
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Correctability.lean#L164-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Correctability.lean#L164-L182

import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Correctability
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.StabilizerCode.exists_finiteKrausCorrectable_iff_pairProductCriterion_on_support
    {α : Type v} [Fintype α]
    (Q : SourceValidBinary ι) (E : α → Binary ι) (amp : α → Complex)
    (hcomplete : (binaryPauliKrausFamily E amp).Complete) :
    (∃ recovery : Semantics.QuantumChannel
          (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι),
      Semantics.FiniteKrausCorrectable α
        (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι)
        Q.1.code (binaryPauliKrausFamily E amp) recovery) ↔
    ∀ a b, amp a ≠ 0 → amp b ≠ 0 →
      Q.1.InGeneratedGroupUpToSign
          (binaryMul (binaryDagger (E a)) (E b)) ∨
      ¬ Q.1.InBinaryNormalizer
          (binaryMul (binaryDagger (E a)) (E b)) := by sorry
