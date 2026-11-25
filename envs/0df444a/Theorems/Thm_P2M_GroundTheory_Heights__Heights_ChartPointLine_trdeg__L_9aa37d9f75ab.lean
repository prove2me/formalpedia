-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartPointLine_trdeg__L_9aa37d9f75ab
-- name    : P2M_GroundTheory_Heights__Heights_ChartPointLine_trdeg__L_9aa37d9f75ab
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:10:16.705785+00:00
-- url     : https://prove2.me/theorems/588b4a81-1582-537f-99ac-b2e80e7a6f61
-- title:
--   P2 M Ground Theory Heights  Heights Chart Point Line trdeg  L 9aa37d9f75ab: P2 M Ground Theory Heights  Heights Chart Point Line trdeg  L 9aa37d9f75ab
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Point Line trdeg  L 9aa37d9f75ab construction uses the P2 M Ground Theory Heights  Heights Chart Point Line trdeg  L 9aa37d9f75ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsChartPointSeparable.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsChartPointSeparable.lean#L80-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_OfFreeParAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartPointSeparable
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartPointLine

theorem P2M_GroundTheory_Heights__Heights_ChartPointLine_trdeg__L_9aa37d9f75ab (j₀ : Fin 2) (hj₀ : ηL j₀ ≠ 0) :
    Algebra.trdeg ℚ (Algebra.adjoin ℚ (Set.range fun m => ηL m * (ηL j₀)⁻¹)) ≤ ((1 : ℕ) : Cardinal) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartPointLine».«trdeg_ηL» := P2M_GroundTheory_Heights__Heights_ChartPointLine_trdeg__L_9aa37d9f75ab
