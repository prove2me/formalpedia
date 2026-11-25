-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_ballSet_eq_smul_e58df8654d39
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_ballSet_eq_smul_e58df8654d39
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:38:17.854936+00:00
-- url     : https://prove2.me/theorems/d723003e-ec07-412c-a7bc-cda10c9a0b0c
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean ball Set eq smul e58df8654d39: P2 M Ground Theory Heights  Heights Sphere Mean ball Set eq smul e58df8654d39
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean ball Set eq smul e58df8654d39 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean ball Set eq smul e58df8654d39 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L71-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
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
open MeasureTheory Measure Set
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean

theorem P2M_GroundTheory_Heights__Heights_SphereMean_ballSet_eq_smul_e58df8654d39 {n : ℕ} {s : ℝ} (hs : 0 < s) : ballSet n s = √s • ballSet n 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«ballSet_eq_smul» := P2M_GroundTheory_Heights__Heights_SphereMean_ballSet_eq_smul_e58df8654d39
