-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowHt_zero_groups_77d7baeecfd0
-- name    : P2M_GroundTheory_Heights__Heights_chowHt_zero_groups_77d7baeecfd0
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:04.030656+00:00
-- url     : https://prove2.me/theorems/f72379cd-1f40-4cd3-aed8-11bfa561312a
-- title:
--   P2 M Ground Theory Heights  Heights chow Ht zero groups 77d7baeecfd0: P2 M Ground Theory Heights  Heights chow Ht zero groups 77d7baeecfd0
-- statement:
--   The P2 M Ground Theory Heights  Heights chow Ht zero groups 77d7baeecfd0 construction uses the P2 M Ground Theory Heights  Heights chow Ht zero groups 77d7baeecfd0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L139-L141

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
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
open MvPolynomial MeasureTheory NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_chowHt_zero_groups_77d7baeecfd0 (H : ArchData K n) (δ : ℕ) (g : MvPolynomial (Fin 0 × Fin n) K) :
    chowHt H 0 δ g = chowHt H 0 0 g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chowHt_zero_groups» := P2M_GroundTheory_Heights__Heights_chowHt_zero_groups_77d7baeecfd0
