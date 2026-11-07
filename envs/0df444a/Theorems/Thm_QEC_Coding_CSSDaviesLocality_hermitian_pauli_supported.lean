-- Prove2me | Theorems.Thm_QEC_Coding_CSSDaviesLocality_hermitian_pauli_supported
-- name    : QEC.Coding.CSSDaviesLocality.hermitian_pauli_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:27:40.815442+00:00
-- url     : https://prove2.me/theorems/05e598c7-c7eb-475f-ab9b-5f6bf42436c6
-- title:
--   CSSDavies Locality: hermitian pauli supported
-- statement:
--   The CSSDavies Locality construction uses the hermitian pauli supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/DaviesLocality.lean#L41-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/DaviesLocality.lean#L41-L44

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

theorem QEC.Coding.CSSDaviesLocality.hermitian_pauli_supported (S : FiniteSubsystem ι) (E : Binary ι)
    (hE : support E ⊆ S.selected) :
    S.OperatorSupportedOnRegister (toHermitianQubitOperator E) := by sorry
