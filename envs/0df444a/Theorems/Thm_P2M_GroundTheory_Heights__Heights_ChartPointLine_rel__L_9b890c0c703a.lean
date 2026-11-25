-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartPointLine_rel__L_9b890c0c703a
-- name    : P2M_GroundTheory_Heights__Heights_ChartPointLine_rel__L_9b890c0c703a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:16:14.656547+00:00
-- url     : https://prove2.me/theorems/a746f357-eb4c-5a09-9ec4-f58ccd8b5d4a
-- title:
--   P2 M Ground Theory Heights  Heights Chart Point Line rel  L 9b890c0c703a: P2 M Ground Theory Heights  Heights Chart Point Line rel  L 9b890c0c703a
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Point Line rel  L 9b890c0c703a construction uses the P2 M Ground Theory Heights  Heights Chart Point Line rel  L 9b890c0c703a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsChartPointSeparable.lean#L66-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsChartPointSeparable.lean#L66-L73

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

theorem P2M_GroundTheory_Heights__Heights_ChartPointLine_rel__L_9b890c0c703a : ∀ i : Fin 1, ∑ m, algebraMap KL KL (uL (i, m)) * ηL m = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartPointLine».«rel_ηL» := P2M_GroundTheory_Heights__Heights_ChartPointLine_rel__L_9b890c0c703a
