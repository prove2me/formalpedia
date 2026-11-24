-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_liftForm_facts_3c10203679d9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_liftForm_facts_3c10203679d9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:40.235021+00:00
-- url     : https://prove2.me/theorems/673119d9-fb0a-41aa-bf64-1c8fc57691f9
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR comap lift Form facts 3c10203679d9: P2 M Ground Theory Heights  Heights Numbers DVR comap lift Form facts 3c10203679d9
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR comap lift Form facts 3c10203679d9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR comap lift Form facts 3c10203679d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L87-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/LiftFormNotMemBlowUpOf.lean#L87-L95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]
variable {J : Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_liftForm_facts_3c10203679d9 {P : Ideal (MRing ι R)} {u : J → MRing ι R}
    {W : Ideal (MRing (extIdx ι J) R)} (hW : W.IsPrime) (hQW : blowUpOf P u ≤ W) (hrel : IsRelevant W) :
    (W.comap (liftForm (J := J))).IsPrime ∧ P ≤ W.comap (liftForm (J := J)) ∧
      IsRelevant (W.comap (liftForm (J := J))) ∧ ∃ j, (newVar j : MRing (extIdx ι J) R) ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«comap_liftForm_facts» := P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_liftForm_facts_3c10203679d9
