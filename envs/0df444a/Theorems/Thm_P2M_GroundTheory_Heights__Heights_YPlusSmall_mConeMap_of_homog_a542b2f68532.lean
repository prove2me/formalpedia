-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSmall_mConeMap_of_homog_a542b2f68532
-- name    : P2M_GroundTheory_Heights__Heights_YPlusSmall_mConeMap_of_homog_a542b2f68532
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:43:52.556066+00:00
-- url     : https://prove2.me/theorems/dcd08be0-a9ac-47ad-b145-1b03a0364def
-- title:
--   P2 M Ground Theory Heights  Heights YPlus Small m Cone Map of homog a542b2f68532: P2 M Ground Theory Heights  Heights YPlus Small m Cone Map of homog a542b2f68532
-- statement:
--   The P2 M Ground Theory Heights  Heights YPlus Small m Cone Map of homog a542b2f68532 construction uses the P2 M Ground Theory Heights  Heights YPlus Small m Cone Map of homog a542b2f68532 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSmall.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSmall.lean#L38-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSmall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSmall
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_YPlusSmall_mConeMap_of_homog_a542b2f68532 {Ω : Type} [Field Ω] {f : MvPolynomial (Coord n) ℤ} {e : ι → ℕ}
    (hf : Geo.IsMultiHomog (ι := blockIdx n) f e) (y : Coord n → Ω) :
    Geo.mConeMap (ι := blockIdx n) y f = C (aeval y f) * ∏ k, X k ^ e k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«YPlusSmall».«mConeMap_of_homog» := P2M_GroundTheory_Heights__Heights_YPlusSmall_mConeMap_of_homog_a542b2f68532
