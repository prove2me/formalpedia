-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_YPlusSmall_eval_map_int_f9e852c2cdf5
-- name    : P2M_GroundTheory_Heights__Heights_YPlusSmall_eval_map_int_f9e852c2cdf5
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:43:58.00582+00:00
-- url     : https://prove2.me/theorems/7adab7fb-ebb4-47f0-8e5f-37bdfbc2cef3
-- title:
--   P2 M Ground Theory Heights  Heights YPlus Small eval map int f9e852c2cdf5: P2 M Ground Theory Heights  Heights YPlus Small eval map int f9e852c2cdf5
-- statement:
--   The P2 M Ground Theory Heights  Heights YPlus Small eval map int f9e852c2cdf5 construction uses the P2 M Ground Theory Heights  Heights YPlus Small eval map int f9e852c2cdf5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSmall.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PYPlusSmall.lean#L69-L71

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

theorem P2M_GroundTheory_Heights__Heights_YPlusSmall_eval_map_int_f9e852c2cdf5 {σ : Type*} (z : σ → ℂ) (F : MvPolynomial σ ℤ) :
    eval z (map (Int.castRingHom ℂ) F) = aeval z F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«YPlusSmall».«eval_map_int» := P2M_GroundTheory_Heights__Heights_YPlusSmall_eval_map_int_f9e852c2cdf5
