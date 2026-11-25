-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integral_ballSet_neg_log_fst_5931faaa90cf
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_integral_ballSet_neg_log_fst_5931faaa90cf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:38:25.962907+00:00
-- url     : https://prove2.me/theorems/8ba35810-716a-4cdd-8a65-346eaa76a5ba
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean integral ball Set neg log fst 5931faaa90cf: P2 M Ground Theory Heights  Heights Sphere Mean integral ball Set neg log fst 5931faaa90cf
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean integral ball Set neg log fst 5931faaa90cf construction uses the P2 M Ground Theory Heights  Heights Sphere Mean integral ball Set neg log fst 5931faaa90cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L211-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L211-L224

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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_integral_ballSet_neg_log_fst_5931faaa90cf (m : ℕ) :
    IntegrableOn (fun x : Fin (m + 1) → ℂ => -log ‖x 0‖) (ballSet (m + 1) 1) ∧
      ∫ x in ballSet (m + 1) 1, -log ‖x 0‖ = harmonic (m + 1) / 2 * volume.real (ballSet (m + 1) 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«integral_ballSet_neg_log_fst» := P2M_GroundTheory_Heights__Heights_SphereMean_integral_ballSet_neg_log_fst_5931faaa90cf
