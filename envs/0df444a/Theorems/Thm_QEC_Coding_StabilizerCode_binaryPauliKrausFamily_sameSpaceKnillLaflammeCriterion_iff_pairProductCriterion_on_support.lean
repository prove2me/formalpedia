-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_binaryPauliKrausFamily_sameSpaceKnillLaflammeCriterion_iff_pairProductCriterion_on_support
-- name    : QEC.Coding.StabilizerCode.binaryPauliKrausFamily_sameSpaceKnillLaflammeCriterion_iff_pairProductCriterion_on_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:29:28.358132+00:00
-- url     : https://prove2.me/theorems/9e629143-cc0f-41f2-8313-e9c4fd0355a7
-- title:
--   Stabilizer Code: binary Pauli Kraus Family same Space Knill Laflamme Criterion iff pair Product Criterion on support
-- statement:
--   The same-space Knill-Laflamme criterion for a scaled binary Pauli Kraus family
--   is exactly the stabilizer pair-product criterion on its nonzero-amplitude
--   support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Correctability.lean#L68-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Correctability.lean#L68-L154

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

theorem QEC.Coding.StabilizerCode.binaryPauliKrausFamily_sameSpaceKnillLaflammeCriterion_iff_pairProductCriterion_on_support
    {α : Type v} [Fintype α]
    (Q : SourceValidBinary ι) (E : α → Binary ι) (amp : α → Complex) :
    (binaryPauliKrausFamily E amp).sameSpaceKnillLaflammeCriterion Q.1.code ↔
      ∀ a b, amp a ≠ 0 → amp b ≠ 0 →
        Q.1.InGeneratedGroupUpToSign
            (binaryMul (binaryDagger (E a)) (E b)) ∨
          ¬ Q.1.InBinaryNormalizer
            (binaryMul (binaryDagger (E a)) (E b)) := by sorry
