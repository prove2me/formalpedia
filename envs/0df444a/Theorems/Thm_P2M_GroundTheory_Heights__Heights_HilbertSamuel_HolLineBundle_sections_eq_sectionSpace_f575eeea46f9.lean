-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_HolLineBundle_sections_eq_sectionSpace_f575eeea46f9
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_HolLineBundle_sections_eq_sectionSpace_f575eeea46f9
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:31.980897+00:00
-- url     : https://prove2.me/theorems/1793d54e-0bf9-5e89-9839-d136ef3f1768
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Hol Line Bundle sections eq section Space f575eeea46f9: P2 M Ground Theory Heights  Heights Hilbert Samuel Hol Line Bundle sections eq section Space
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Hol Line Bundle sections eq section Space f575eeea46f9 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Hol Line Bundle sections eq section Space f575eeea46f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/HolLineBundleToAltTransition.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/HolLineBundleToAltTransition.lean#L36-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_SectionL2NormSq
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_HolLineBundleToAltTransition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ComplexConjugate ENNReal ContDiff
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
open GroundTheory.Heights₂.Heights.HilbertSamuel.HolLineBundle

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_HolLineBundle_sections_eq_sectionSpace_f575eeea46f9 (L : HolLineBundle A) (n : ℕ) :
    L.sections n = IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.sectionSpace L.toIndefiniteRowSideFullHecke n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«HolLineBundle».«sections_eq_sectionSpace» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_HolLineBundle_sections_eq_sectionSpace_f575eeea46f9
