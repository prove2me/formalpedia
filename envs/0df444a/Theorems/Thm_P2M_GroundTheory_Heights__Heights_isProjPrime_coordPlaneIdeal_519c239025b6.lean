-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_coordPlaneIdeal_519c239025b6
-- name    : P2M_GroundTheory_Heights__Heights_isProjPrime_coordPlaneIdeal_519c239025b6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:04.854442+00:00
-- url     : https://prove2.me/theorems/52e13a90-88de-47a5-b704-9489c76d58c4
-- title:
--   P2 M Ground Theory Heights  Heights is Proj Prime coord Plane Ideal 519c239025b6: P2 M Ground Theory Heights  Heights is Proj Prime coord Plane Ideal 519c239025b6
-- statement:
--   The P2 M Ground Theory Heights  Heights is Proj Prime coord Plane Ideal 519c239025b6 construction uses the P2 M Ground Theory Heights  Heights is Proj Prime coord Plane Ideal 519c239025b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L48-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L48-L56

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

theorem P2M_GroundTheory_Heights__Heights_isProjPrime_coordPlaneIdeal_519c239025b6 {m : ℕ} (hm : 0 < m) (k : ℕ) :
    IsProjPrime (coordPlaneIdeal m k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isProjPrime_coordPlaneIdeal» := P2M_GroundTheory_Heights__Heights_isProjPrime_coordPlaneIdeal_519c239025b6
