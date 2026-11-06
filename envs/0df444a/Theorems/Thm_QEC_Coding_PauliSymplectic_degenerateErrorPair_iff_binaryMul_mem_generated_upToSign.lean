-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_degenerateErrorPair_iff_binaryMul_mem_generated_upToSign
-- name    : QEC.Coding.PauliSymplectic.degenerateErrorPair_iff_binaryMul_mem_generated_upToSign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:26:49.791193+00:00
-- url     : https://prove2.me/theorems/a036031d-b0a6-438a-ba3b-2da317eece3b
-- title:
--   Pauli Symplectic: degenerate Error Pair iff binary Mul mem generated up To Sign
-- statement:
--   Source-facing degeneracy in either pair-product convention.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1552-L1556
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1552-L1556

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

theorem QEC.Coding.PauliSymplectic.degenerateErrorPair_iff_binaryMul_mem_generated_upToSign
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E F : Binary ι) :
    DegenerateErrorPair generators E F ↔
      InGeneratedStabilizerUpToSign generators (binaryMul E F) := by sorry
