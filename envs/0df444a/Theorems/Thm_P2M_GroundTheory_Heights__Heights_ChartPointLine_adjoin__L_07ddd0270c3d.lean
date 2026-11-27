-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartPointLine_adjoin__L_07ddd0270c3d
-- name    : P2M_GroundTheory_Heights__Heights_ChartPointLine_adjoin__L_07ddd0270c3d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:17:11.405619+00:00
-- url     : https://prove2.me/theorems/a15e9b20-a01a-5f89-8048-dda3df4b2d77
-- title:
--   P2 M Ground Theory Heights  Heights Chart Point Line adjoin  L 07ddd0270c3d: P2 M Ground Theory Heights  Heights Chart Point Line adjoin  L 07ddd0270c3d
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Point Line adjoin  L 07ddd0270c3d construction uses the P2 M Ground Theory Heights  Heights Chart Point Line adjoin  L 07ddd0270c3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsChartPointSeparable.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsChartPointSeparable.lean#L62-L64

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

theorem P2M_GroundTheory_Heights__Heights_ChartPointLine_adjoin__L_07ddd0270c3d : IntermediateField.adjoin KL (Set.range ηL) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartPointLine».«adjoin_ηL» := P2M_GroundTheory_Heights__Heights_ChartPointLine_adjoin__L_07ddd0270c3d
