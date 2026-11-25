-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_chartLin_self_072b523c4f30
-- name    : P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_chartLin_self_072b523c4f30
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:12.573466+00:00
-- url     : https://prove2.me/theorems/498c7ef8-f928-42f7-8b68-e479e996e4bb
-- title:
--   P2 M Ground Theory Heights  Heights Chart Norm Alg Closed chart Lin self 072b523c4f30: P2 M Ground Theory Heights  Heights Chart Norm Alg Closed chart Lin self 072b523c4f30
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Norm Alg Closed chart Lin self 072b523c4f30 construction uses the P2 M Ground Theory Heights  Heights Chart Norm Alg Closed chart Lin self 072b523c4f30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartNormAlgClosed.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartNormAlgClosed.lean#L44-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormAlgClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormSep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartNormAlgClosed
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
open GroundTheory.Heights₂.Heights.ChartNormAlgClosed
variable {F : Type} [Field F] {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
  (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_chartLin_self_072b523c4f30 : chartLin I t e t = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartNormAlgClosed».«chartLin_self» := P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_chartLin_self_072b523c4f30
