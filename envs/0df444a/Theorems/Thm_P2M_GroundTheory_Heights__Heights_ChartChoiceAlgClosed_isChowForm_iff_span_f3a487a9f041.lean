-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_isChowForm_iff_span_f3a487a9f041
-- name    : P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_isChowForm_iff_span_f3a487a9f041
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:17:32.589584+00:00
-- url     : https://prove2.me/theorems/ad315e6e-6e21-4a47-88e1-4a28977e8b96
-- title:
--   P2 M Ground Theory Heights  Heights Chart Choice Alg Closed is Chow Form iff span f3a487a9f041: P2 M Ground Theory Heights  Heights Chart Choice Alg Closed is Chow Form iff span f3a487a9f041
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Choice Alg Closed is Chow Form iff span f3a487a9f041 construction uses the P2 M Ground Theory Heights  Heights Chart Choice Alg Closed is Chow Form iff span f3a487a9f041 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartChoiceAlgClosed.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartChoiceAlgClosed.lean#L15-L29

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

theorem P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_isChowForm_iff_span_f3a487a9f041 {P : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {g : MvPolynomial (Fin k × Fin n) F} :
    IsChowForm P k g ↔ g ≠ 0 ∧ incIdeal P k = Ideal.span {g} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartChoiceAlgClosed».«isChowForm_iff_span» := P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_isChowForm_iff_span_f3a487a9f041
