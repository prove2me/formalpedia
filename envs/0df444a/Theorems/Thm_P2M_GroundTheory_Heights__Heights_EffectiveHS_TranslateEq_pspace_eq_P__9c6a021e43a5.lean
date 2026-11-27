-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_TranslateEq_pspace_eq_P__9c6a021e43a5
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_TranslateEq_pspace_eq_P__9c6a021e43a5
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:11:08.886839+00:00
-- url     : https://prove2.me/theorems/d2fb1bd1-ff02-526f-a505-b68e9f5c757c
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS Translate Eq pspace eq P  9c6a021e43a5: P2 M Ground Theory Heights  Heights Effective HS Translate Eq pspace eq P  9c6a021e43a5
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS Translate Eq pspace eq P  9c6a021e43a5 construction uses the P2 M Ground Theory Heights  Heights Effective HS Translate Eq pspace eq P  9c6a021e43a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/MemSectionsOfHolLineBundleEquiv.lean#L156-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/MemSectionsOfHolLineBundleEquiv.lean#L156-L162

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_MemSectionsOfHolLineBundleEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.EffectiveHS
open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.EffectiveHS (topForms topFormWeightedL2 twist wAdd fsPhi HermSpace FSData HSData
  secMul l2n tuples jacDet)
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.EffectiveHS.TranslateEq
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
variable {Y : Type} [TopologicalSpace Y]

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_TranslateEq_pspace_eq_P__9c6a021e43a5 (d : HSData A Y) (s : Fin D → Fin d.W.n → ℂ) :
    Pspace (fun i => d.W.sec (s i)) (d.V D).space d.T = d.Pσ s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«TranslateEq».«pspace_eq_Pσ» := P2M_GroundTheory_Heights__Heights_EffectiveHS_TranslateEq_pspace_eq_P__9c6a021e43a5
