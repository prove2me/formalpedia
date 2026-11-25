-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_IsomInvariance_exists_ratSection_7ff018dbcb48
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_IsomInvariance_exists_ratSection_7ff018dbcb48
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:28.055011+00:00
-- url     : https://prove2.me/theorems/8234cdbf-440e-4538-af0b-981245205974
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Isom Invariance exists rat Section 7ff018dbcb48: P2 M Ground Theory Heights  Heights Hilbert Samuel Isom Invariance exists rat Section 7ff018dbcb48
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Isom Invariance exists rat Section 7ff018dbcb48 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Isom Invariance exists rat Section 7ff018dbcb48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PIsomInvariance.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PIsomInvariance.lean#L18-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIsomInvariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
open GroundTheory.Heights₂.Heights.HilbertSamuel.IsomInvariance
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_IsomInvariance_exists_ratSection_7ff018dbcb48 {P : Ideal (MRing ι)} (hP : P.IsPrime) (hrel : IsRelevant P) (B : HermLine ι) :
    ∃ s t : MRing ι, IsRatSectionOn P B s t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«IsomInvariance».«exists_ratSection» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_IsomInvariance_exists_ratSection_7ff018dbcb48
