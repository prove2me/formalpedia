-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_norm_fst_le_one_2162d3b3bc0f
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_norm_fst_le_one_2162d3b3bc0f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:35.632114+00:00
-- url     : https://prove2.me/theorems/ddb767ac-e1a9-4a4d-8a2f-17d49cc700da
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean norm fst le one 2162d3b3bc0f: P2 M Ground Theory Heights  Heights Sphere Mean norm fst le one 2162d3b3bc0f
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean norm fst le one 2162d3b3bc0f construction uses the P2 M Ground Theory Heights  Heights Sphere Mean norm fst le one 2162d3b3bc0f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L206-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L206-L209

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
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
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean

theorem P2M_GroundTheory_Heights__Heights_SphereMean_norm_fst_le_one_2162d3b3bc0f {m : ℕ} {x : Fin (m + 1) → ℂ} (hx : x ∈ ballSet (m + 1) 1) : ‖x 0‖ ≤ 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«norm_fst_le_one» := P2M_GroundTheory_Heights__Heights_SphereMean_norm_fst_le_one_2162d3b3bc0f
