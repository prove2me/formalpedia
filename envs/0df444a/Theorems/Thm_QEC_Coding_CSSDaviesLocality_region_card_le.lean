-- Prove2me | Theorems.Thm_QEC_Coding_CSSDaviesLocality_region_card_le
-- name    : QEC.Coding.CSSDaviesLocality.region_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:42:40.671768+00:00
-- url     : https://prove2.me/theorems/d4be0c77-1455-42d8-a692-891bfb6be984
-- title:
--   CSSDavies Locality: region card le
-- statement:
--   The CSSDavies Locality construction uses the region card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/DaviesLocality.lean#L217-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CSS/DaviesLocality.lean#L217-L227

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

theorem QEC.Coding.CSSDaviesLocality.region_card_le (q : ι) (d w : Nat) (hd : (incident P Q q).card ≤ d)
    (hw : ∀ j, (rowSupport P Q j).card ≤ w) : (region P Q q).card ≤ 1+d*w := by sorry
