-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_hasDerivAt_primG_4aa3708b7524
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_hasDerivAt_primG_4aa3708b7524
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:34.968634+00:00
-- url     : https://prove2.me/theorems/f9e5fbe0-5d95-547c-972b-ac032c80fe37
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean has Deriv At prim G 4aa3708b7524: P2 M Ground Theory Heights  Heights Sphere Mean has Deriv At prim G 4aa3708b7524
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean has Deriv At prim G 4aa3708b7524 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean has Deriv At prim G 4aa3708b7524 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanCalc.lean#L61-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanCalc.lean#L61-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc
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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_hasDerivAt_primG_4aa3708b7524 (m : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (primG m) ((1 - s) ^ m * log s) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«hasDerivAt_primG» := P2M_GroundTheory_Heights__Heights_SphereMean_hasDerivAt_primG_4aa3708b7524
