-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_homogeneousComponent_aeval_coordPlaneSubst_6be6f2ef863d
-- name    : P2M_GroundTheory_Heights__Heights_homogeneousComponent_aeval_coordPlaneSubst_6be6f2ef863d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:53.463047+00:00
-- url     : https://prove2.me/theorems/06de5bae-853c-42cd-aefb-503548a1a611
-- title:
--   P2 M Ground Theory Heights  Heights homogeneous Component aeval coord Plane Subst 6be6f2ef863d: P2 M Ground Theory Heights  Heights homogeneous Component aeval coord Plane Subst 6be6f2ef863d
-- statement:
--   The P2 M Ground Theory Heights  Heights homogeneous Component aeval coord Plane Subst 6be6f2ef863d construction uses the P2 M Ground Theory Heights  Heights homogeneous Component aeval coord Plane Subst 6be6f2ef863d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L22-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L22-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_homogeneousComponent_aeval_coordPlaneSubst_6be6f2ef863d (m k d : ℕ) (f : MvPolynomial (Fin (m + k)) ℂ) :
    homogeneousComponent d (aeval (coordPlaneSubst m k) f) =
      aeval (coordPlaneSubst m k) (homogeneousComponent d f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«homogeneousComponent_aeval_coordPlaneSubst» := P2M_GroundTheory_Heights__Heights_homogeneousComponent_aeval_coordPlaneSubst_6be6f2ef863d
