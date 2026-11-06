-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_checkDistinguishes_range_iff_exists_syndromeBit_eq_one
-- name    : QEC.Coding.PauliSymplectic.checkDistinguishes_range_iff_exists_syndromeBit_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:27:26.977202+00:00
-- url     : https://prove2.me/theorems/7e0be036-64bc-4b6e-a308-76ca954d12e4
-- title:
--   Pauli Symplectic: check Distinguishes range iff exists syndrome Bit eq one
-- statement:
--   Existential check separation is exactly the existence of a one syndrome bit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1688-L1697
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1688-L1697

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
omit [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.checkDistinguishes_range_iff_exists_syndromeBit_eq_one
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E : Binary ι) :
    checkDistinguishes (Set.range generators) E ↔
      ∃ j, stabilizerSyndromeBit (generators j) E = 1 := by sorry
