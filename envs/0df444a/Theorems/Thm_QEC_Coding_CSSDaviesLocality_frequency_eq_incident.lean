-- Prove2me | Theorems.Thm_QEC_Coding_CSSDaviesLocality_frequency_eq_incident
-- name    : QEC.Coding.CSSDaviesLocality.frequency_eq_incident
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:28:33.66321+00:00
-- url     : https://prove2.me/theorems/1a4a9038-f823-40ac-83d4-1a3c1b547b72
-- title:
--   CSSDavies Locality: frequency eq incident
-- statement:
--   Equality to the true local-H component, with every equal-frequency term retained.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/DaviesLocality.lean#L192-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/DaviesLocality.lean#L192-L200

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

theorem QEC.Coding.CSSDaviesLocality.frequency_eq_incident (q : ι) (a : Axis) (ω : ℝ) :
    actualFrequency (hamiltonian P Q) (hamiltonian_symmetric P Q) (coupling q a) ω =
      actualFrequency (incidentHamiltonian P Q q) (incidentHamiltonian_symmetric P Q q) (coupling q a) ω := by sorry
