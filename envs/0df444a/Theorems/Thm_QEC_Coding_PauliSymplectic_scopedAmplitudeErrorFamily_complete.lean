-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_scopedAmplitudeErrorFamily_complete
-- name    : QEC.Coding.PauliSymplectic.scopedAmplitudeErrorFamily_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:23:26.232319+00:00
-- url     : https://prove2.me/theorems/8d589669-8874-4f15-ade3-dcc126b4a975
-- title:
--   Pauli Symplectic: scoped Amplitude Error Family complete
-- statement:
--   Amplitude normalization gives finite-Kraus completeness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2373-L2383
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L2373-L2383

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

theorem QEC.Coding.PauliSymplectic.scopedAmplitudeErrorFamily_complete
    {t : Nat}
    (amp : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t} → Complex)
    (hamp : ∑ P : {P : Binary ι // P ∈ scopedByWeight (ι := ι) t},
      star (amp P) * amp P = 1) :
    (scopedAmplitudeErrorFamily (ι := ι) t amp).Complete := by sorry
