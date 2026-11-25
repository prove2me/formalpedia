-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_eval_map_splitFirst_2e15af932b36
-- name    : P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_eval_map_splitFirst_2e15af932b36
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:17:55.094445+00:00
-- url     : https://prove2.me/theorems/9ea8849b-d6ce-46d9-8115-7ef1224398e9
-- title:
--   P2 M Ground Theory Heights  Heights Chart Choice Alg Closed eval map split First 2e15af932b36: P2 M Ground Theory Heights  Heights Chart Choice Alg Closed eval map split First 2e15af932b36
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Choice Alg Closed eval map split First 2e15af932b36 construction uses the P2 M Ground Theory Heights  Heights Chart Choice Alg Closed eval map split First 2e15af932b36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartChoiceAlgClosed.lean#L89-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartChoiceAlgClosed.lean#L89-L101

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

theorem P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_eval_map_splitFirst_2e15af932b36 (J : Ideal (MvPolynomial (Fin e × Fin n) F)) (t : Fin n → F)
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) :
    eval (fun m => Ideal.Quotient.mk J (C (t m))) (map (Ideal.Quotient.mk J) (splitFirst F e n f)) =
      Ideal.Quotient.mk J (specFirst f t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartChoiceAlgClosed».«eval_map_splitFirst» := P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_eval_map_splitFirst_2e15af932b36
