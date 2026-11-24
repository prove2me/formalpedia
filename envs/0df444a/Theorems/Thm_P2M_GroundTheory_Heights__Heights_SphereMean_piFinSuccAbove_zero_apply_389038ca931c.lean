-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_piFinSuccAbove_zero_apply_389038ca931c
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_piFinSuccAbove_zero_apply_389038ca931c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:02.483688+00:00
-- url     : https://prove2.me/theorems/4fda6cac-2331-47c6-99c4-6c376d9cbd8c
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean pi Fin Succ Above zero apply 389038ca931c: P2 M Ground Theory Heights  Heights Sphere Mean pi Fin Succ Above zero apply 389038ca931c
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean pi Fin Succ Above zero apply 389038ca931c construction uses the P2 M Ground Theory Heights  Heights Sphere Mean pi Fin Succ Above zero apply 389038ca931c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L19-L21

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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_piFinSuccAbove_zero_apply_389038ca931c {m : ℕ} (x : Fin (m + 1) → ℂ) :
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0 x = (x 0, Fin.tail x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«piFinSuccAbove_zero_apply» := P2M_GroundTheory_Heights__Heights_SphereMean_piFinSuccAbove_zero_apply_389038ca931c
