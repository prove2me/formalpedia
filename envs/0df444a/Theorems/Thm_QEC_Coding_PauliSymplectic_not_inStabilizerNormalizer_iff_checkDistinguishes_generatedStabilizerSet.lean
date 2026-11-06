-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_not_inStabilizerNormalizer_iff_checkDistinguishes_generatedStabilizerSet
-- name    : QEC.Coding.PauliSymplectic.not_inStabilizerNormalizer_iff_checkDistinguishes_generatedStabilizerSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:27:31.341664+00:00
-- url     : https://prove2.me/theorems/c9c83983-cdf2-4b04-ab54-b461f4517031
-- title:
--   Pauli Symplectic: not in Stabilizer Normalizer iff check Distinguishes generated Stabilizer Set
-- statement:
--   Failure of normalizer membership is witnessed by a generated stabilizer check.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1732-L1737
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PauliSemantics.lean#L1732-L1737

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

theorem QEC.Coding.PauliSymplectic.not_inStabilizerNormalizer_iff_checkDistinguishes_generatedStabilizerSet
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E : Binary ι) :
    ¬ InStabilizerNormalizer generators E ↔
      checkDistinguishes (generatedStabilizerSet generators) E := by sorry
