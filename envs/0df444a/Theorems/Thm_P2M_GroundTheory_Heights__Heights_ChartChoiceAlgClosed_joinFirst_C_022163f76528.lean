-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_joinFirst_C_022163f76528
-- name    : P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_joinFirst_C_022163f76528
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:17:33.701036+00:00
-- url     : https://prove2.me/theorems/20fef2e8-185f-4207-b039-f40ed30b38dd
-- title:
--   P2 M Ground Theory Heights  Heights Chart Choice Alg Closed join First C 022163f76528: P2 M Ground Theory Heights  Heights Chart Choice Alg Closed join First C 022163f76528
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Choice Alg Closed join First C 022163f76528 construction uses the P2 M Ground Theory Heights  Heights Chart Choice Alg Closed join First C 022163f76528 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartChoiceAlgClosed.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartChoiceAlgClosed.lean#L52-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartChoiceAlgClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartChoiceAlgClosed
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
open GroundTheory.Heights₂.Heights.ChartChoiceAlgClosed
variable {F : Type} [Field F] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_joinFirst_C_022163f76528 (a : MvPolynomial (Fin e × Fin n) F) :
    joinFirst F e n (C a) = rename (shiftVar e n) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartChoiceAlgClosed».«joinFirst_C» := P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_joinFirst_C_022163f76528
