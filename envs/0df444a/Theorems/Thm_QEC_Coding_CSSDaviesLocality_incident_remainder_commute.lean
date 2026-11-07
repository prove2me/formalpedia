-- Prove2me | Theorems.Thm_QEC_Coding_CSSDaviesLocality_incident_remainder_commute
-- name    : QEC.Coding.CSSDaviesLocality.incident_remainder_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:27:28.707138+00:00
-- url     : https://prove2.me/theorems/7643d572-c318-4972-8a80-2ff9d6df2652
-- title:
--   CSSDavies Locality: incident remainder commute
-- statement:
--   The CSSDavies Locality construction uses the incident remainder commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/DaviesLocality.lean#L145-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/DaviesLocality.lean#L145-L153

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
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
variable (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
include horth

theorem QEC.Coding.CSSDaviesLocality.incident_remainder_commute (q : ι) : Commute (incidentHamiltonian P Q q) (remainderHamiltonian P Q q) := by sorry
