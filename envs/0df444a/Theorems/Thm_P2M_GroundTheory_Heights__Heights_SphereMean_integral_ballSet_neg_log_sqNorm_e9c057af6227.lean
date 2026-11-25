-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integral_ballSet_neg_log_sqNorm_e9c057af6227
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_integral_ballSet_neg_log_sqNorm_e9c057af6227
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:38:45.49481+00:00
-- url     : https://prove2.me/theorems/fb148cb1-385c-4373-ad2c-79ea74f5dc4e
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean integral ball Set neg log sq Norm e9c057af6227: P2 M Ground Theory Heights  Heights Sphere Mean integral ball Set neg log sq Norm e9c057af6227
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean integral ball Set neg log sq Norm e9c057af6227 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean integral ball Set neg log sq Norm e9c057af6227 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L226-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L226-L235

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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_integral_ballSet_neg_log_sqNorm_e9c057af6227 (m : ℕ) :
    IntegrableOn (fun x : Fin (m + 1) → ℂ => -log (sqNorm x)) (ballSet (m + 1) 1) ∧
      ∫ x in ballSet (m + 1) 1, -log (sqNorm x) = 1 / (m + 1) * volume.real (ballSet (m + 1) 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«integral_ballSet_neg_log_sqNorm» := P2M_GroundTheory_Heights__Heights_SphereMean_integral_ballSet_neg_log_sqNorm_e9c057af6227
