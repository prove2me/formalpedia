-- Prove2me | Theorems.Thm_QEC_Coding_CSSDaviesLocality_pauli_supported
-- name    : QEC.Coding.CSSDaviesLocality.pauli_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:21:06.784247+00:00
-- url     : https://prove2.me/theorems/380989b8-89c3-41ff-9bf8-7087749a8599
-- title:
--   CSSDavies Locality: pauli supported
-- statement:
--   Every binary Pauli is genuinely an identity extension from any containing region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/DaviesLocality.lean#L16-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/DaviesLocality.lean#L16-L39

import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.CSSDaviesLocality
open Classical PauliSymplectic QEC.Semantics QEC.Locality QEC.Semantics.Davies
open scoped BigOperators
noncomputable section
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι] [Fintype κP] [Fintype κQ]

theorem QEC.Coding.CSSDaviesLocality.pauli_supported (S : FiniteSubsystem ι) (E : Binary ι) (hE : support E ⊆ S.selected) :
    S.OperatorSupportedOnRegister (toQubitOperator E) := by sorry
