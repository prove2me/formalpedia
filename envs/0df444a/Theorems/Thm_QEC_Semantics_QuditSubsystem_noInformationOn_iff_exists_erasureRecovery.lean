-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_iff_exists_erasureRecovery
-- name    : QEC.Semantics.QuditSubsystem.noInformationOn_iff_exists_erasureRecovery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:50:59.876358+00:00
-- url     : https://prove2.me/theorems/c7726a11-e1ee-4900-9bed-e50a899c005c
-- title:
--   Qudit Subsystem: no Information On iff exists erasure Recovery
-- statement:
--   For strictly positive finite local dimensions, local measurement
--   indistinguishability is exactly correctability of the concrete register erasure
--   channel.  This is an internal bridge theorem, not a BPT tradeoff statement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1361-L1373
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1361-L1373

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.noInformationOn_iff_exists_erasureRecovery
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (hq : ∀ i, 0 < q i) :
    NoInformationOn C S ↔
      ∃ recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
        Correctable (Qudit.QuditRegister q) S.complementSystem C
          S.erasureChannelFromRegister recovery := by sorry
