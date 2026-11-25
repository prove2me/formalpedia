-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_specFirst_rename_shiftVar_f3b2f9ee6aab
-- name    : P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_specFirst_rename_shiftVar_f3b2f9ee6aab
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:17:42.714522+00:00
-- url     : https://prove2.me/theorems/e9144c8c-c7d5-4be4-b4df-e84a9ad695ed
-- title:
--   P2 M Ground Theory Heights  Heights Chart Choice Alg Closed spec First rename shift Var f3b2f9ee6aab: P2 M Ground Theory Heights  Heights Chart Choice Alg Closed spec First rename shift Var f3b2f9ee6a
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Choice Alg Closed spec First rename shift Var f3b2f9ee6aab construction uses the P2 M Ground Theory Heights  Heights Chart Choice Alg Closed spec First rename shift Var f3b2f9ee6aab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartChoiceAlgClosed.lean#L56-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartChoiceAlgClosed.lean#L56-L64

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

theorem P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_specFirst_rename_shiftVar_f3b2f9ee6aab (q : MvPolynomial (Fin e × Fin n) F) :
    specFirst (rename (shiftVar e n) q) 0 = q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartChoiceAlgClosed».«specFirst_rename_shiftVar» := P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_specFirst_rename_shiftVar_f3b2f9ee6aab
