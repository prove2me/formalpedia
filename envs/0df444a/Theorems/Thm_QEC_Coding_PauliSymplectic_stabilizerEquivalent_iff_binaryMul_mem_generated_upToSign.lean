-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerEquivalent_iff_binaryMul_mem_generated_upToSign
-- name    : QEC.Coding.PauliSymplectic.stabilizerEquivalent_iff_binaryMul_mem_generated_upToSign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:22:39.530348+00:00
-- url     : https://prove2.me/theorems/bcdfeaba-144d-4995-b359-746e64716d95
-- title:
--   Pauli Symplectic: stabilizer Equivalent iff binary Mul mem generated up To Sign
-- statement:
--   The relative-error definition of stabilizer equivalence is exactly the source's
--   `E * F` membership statement once the possible binary global sign is quotiented.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1537-L1548
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1537-L1548

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

theorem QEC.Coding.PauliSymplectic.stabilizerEquivalent_iff_binaryMul_mem_generated_upToSign
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E F : Binary ι) :
    StabilizerEquivalent generators E F ↔
      InGeneratedStabilizerUpToSign generators (binaryMul E F) := by sorry
