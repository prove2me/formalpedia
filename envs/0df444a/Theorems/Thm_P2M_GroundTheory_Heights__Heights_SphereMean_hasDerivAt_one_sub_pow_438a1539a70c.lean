-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_hasDerivAt_one_sub_pow_438a1539a70c
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_hasDerivAt_one_sub_pow_438a1539a70c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:54.18471+00:00
-- url     : https://prove2.me/theorems/13e6a47e-73ae-402b-9892-6520917be0e1
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean has Deriv At one sub pow 438a1539a70c: P2 M Ground Theory Heights  Heights Sphere Mean has Deriv At one sub pow 438a1539a70c
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean has Deriv At one sub pow 438a1539a70c construction uses the P2 M Ground Theory Heights  Heights Sphere Mean has Deriv At one sub pow 438a1539a70c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanCalc.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanCalc.lean#L27-L30

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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_hasDerivAt_one_sub_pow_438a1539a70c (k : ℕ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => (1 - s) ^ k) (-((k : ℝ) * (1 - s) ^ (k - 1))) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«hasDerivAt_one_sub_pow» := P2M_GroundTheory_Heights__Heights_SphereMean_hasDerivAt_one_sub_pow_438a1539a70c
