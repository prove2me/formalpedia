-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_integrable_disc_radial_b2316b4572c9
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_integrable_disc_radial_b2316b4572c9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:10.970298+00:00
-- url     : https://prove2.me/theorems/705bb119-cacb-4274-8f11-3caf3513e118
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean integrable disc radial b2316b4572c9: P2 M Ground Theory Heights  Heights Sphere Mean integrable disc radial b2316b4572c9
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean integrable disc radial b2316b4572c9 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean integrable disc radial b2316b4572c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanDisc.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanDisc.lean#L28-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_integrable_disc_radial_b2316b4572c9 (g : ℝ → ℝ) (hg : ContinuousOn (fun y => y * g y) (Icc 0 1)) :
    Integrable (fun z : ℂ => (Iio (1 : ℝ)).indicator g ‖z‖) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«integrable_disc_radial» := P2M_GroundTheory_Heights__Heights_SphereMean_integrable_disc_radial_b2316b4572c9
