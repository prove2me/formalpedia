-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_volume_fst_eq_zero_062a39c0e25b
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_volume_fst_eq_zero_062a39c0e25b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:39:25.430644+00:00
-- url     : https://prove2.me/theorems/c2025437-a655-5589-a940-b1863e02dce9
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean volume fst eq zero 062a39c0e25b: P2 M Ground Theory Heights  Heights Sphere Mean volume fst eq zero 062a39c0e25b
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean volume fst eq zero 062a39c0e25b construction uses the P2 M Ground Theory Heights  Heights Sphere Mean volume fst eq zero 062a39c0e25b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMean.lean#L31-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMean.lean#L31-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_volume_fst_eq_zero_062a39c0e25b (m : ℕ) : volume {y : Fin (m + 1) → ℂ | y 0 = 0} = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«volume_fst_eq_zero» := P2M_GroundTheory_Heights__Heights_SphereMean_volume_fst_eq_zero_062a39c0e25b
