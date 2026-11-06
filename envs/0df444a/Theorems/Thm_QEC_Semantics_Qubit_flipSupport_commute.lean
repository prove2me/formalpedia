-- Prove2me | Theorems.Thm_QEC_Semantics_Qubit_flipSupport_commute
-- name    : QEC.Semantics.Qubit.flipSupport_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:21:10.773196+00:00
-- url     : https://prove2.me/theorems/8342c88b-7525-4172-b14b-dc6949e6e5f4
-- title:
--   Qubit: flip Support commute
-- statement:
--   Flipping two finite supports commutes on computational-basis bitstrings.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L33-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L33-L36

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
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators
universe u
variable {ι : Type u}

theorem QEC.Semantics.Qubit.flipSupport_commute [DecidableEq ι] (s t : Finset ι) (bits : Bitstring ι) :
    flipSupport s (flipSupport t bits) = flipSupport t (flipSupport s bits) := by sorry
