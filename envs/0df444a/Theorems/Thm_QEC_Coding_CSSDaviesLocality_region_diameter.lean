-- Prove2me | Theorems.Thm_QEC_Coding_CSSDaviesLocality_region_diameter
-- name    : QEC.Coding.CSSDaviesLocality.region_diameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:42:19.386404+00:00
-- url     : https://prove2.me/theorems/703633dc-f348-4c60-8f7b-4679a2c19246
-- title:
--   CSSDavies Locality: region diameter
-- statement:
--   The CSSDavies Locality construction uses the region diameter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/DaviesLocality.lean#L241-L248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/DaviesLocality.lean#L241-L248

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
omit horth

theorem QEC.Coding.CSSDaviesLocality.region_diameter (J : ι → EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 ≤ r)
    (hs : ∀ j, ∀ x ∈ rowSupport P Q j, ∀ y ∈ rowSupport P Q j, dist (J x) (J y) ≤ r)
    (q x y : ι) (hx : x ∈ region P Q q) (hy : y ∈ region P Q q) : dist (J x) (J y) ≤ 2*r := by sorry
