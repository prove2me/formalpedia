-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_pointOf_std_30aaec238417
-- name    : P2M_GroundTheory_Heights__Heights_pointOf_std_30aaec238417
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:50:22.208604+00:00
-- url     : https://prove2.me/theorems/830e9a49-2c22-5d06-b61c-0af83f77f65e
-- title:
--   P2 M Ground Theory Heights  Heights point Of std 30aaec238417: P2 M Ground Theory Heights  Heights point Of std 30aaec238417
-- statement:
--   The P2 M Ground Theory Heights  Heights point Of std 30aaec238417 construction uses the P2 M Ground Theory Heights  Heights point Of std 30aaec238417 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeMassOfFibre.lean#L58-L60

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

theorem P2M_GroundTheory_Heights__Heights_pointOf_std_30aaec238417 {n : ℕ} (y : EuclideanSpace ℂ (Fin n)) :
    (HermNorm.std n).pointOf y = fun i => y i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«pointOf_std» := P2M_GroundTheory_Heights__Heights_pointOf_std_30aaec238417
