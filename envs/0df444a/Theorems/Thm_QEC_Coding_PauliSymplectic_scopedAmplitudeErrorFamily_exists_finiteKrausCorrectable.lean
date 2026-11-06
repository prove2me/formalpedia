-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_scopedAmplitudeErrorFamily_exists_finiteKrausCorrectable
-- name    : QEC.Coding.PauliSymplectic.scopedAmplitudeErrorFamily_exists_finiteKrausCorrectable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:23:41.872885+00:00
-- url     : https://prove2.me/theorems/8cbf463b-a21c-40ca-aa06-f3b52aeb6653
-- title:
--   Pauli Symplectic: scoped Amplitude Error Family exists finite Kraus Correctable
-- statement:
--   Normalized amplitude-weighted scoped Pauli finite-Kraus noise has a recovery.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2428-L2453
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2428-L2453

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

theorem QEC.Coding.PauliSymplectic.scopedAmplitudeErrorFamily_exists_finiteKrausCorrectable
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {dX dZ t : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    (hminZ : MinimumDistance xCode.dual dZ)
    (hbound : 2 * t < min dX dZ)
    (amp : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t} → Complex)
    (hamp : ∑ P : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t},
      star (amp P) * amp P = 1) :
    ∃ recovery : Semantics.QuantumChannel
        (Semantics.Qubit.QubitRegister ι) (Semantics.Qubit.QubitRegister ι),
      Semantics.FiniteKrausCorrectable
        {P : Binary ι // P ∈ scopedByWeight (ι := ι) t}
        (Semantics.Qubit.QubitRegister ι)
        (Semantics.Qubit.QubitRegister ι)
        (binaryCSSQuantumCodeOfDualLe xCode zCode hdual)
        (scopedAmplitudeErrorFamily (ι := ι) t amp)
        recovery := by sorry
