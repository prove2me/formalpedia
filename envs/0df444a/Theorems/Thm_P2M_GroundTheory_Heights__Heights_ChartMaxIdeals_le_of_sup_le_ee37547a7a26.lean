-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_le_of_sup_le_ee37547a7a26
-- name    : P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_le_of_sup_le_ee37547a7a26
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:16:33.739465+00:00
-- url     : https://prove2.me/theorems/5a21f1b1-2d8c-41d4-96bd-4dce9e7c4bf6
-- title:
--   P2 M Ground Theory Heights  Heights Chart Max Ideals le of sup le ee37547a7a26: P2 M Ground Theory Heights  Heights Chart Max Ideals le of sup le ee37547a7a26
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Max Ideals le of sup le ee37547a7a26 construction uses the P2 M Ground Theory Heights  Heights Chart Max Ideals le of sup le ee37547a7a26 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartMaxIdeals.lean#L91-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartMaxIdeals.lean#L91-L98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartMaxIdeals
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
open GroundTheory.Heights₂.Heights.ChartMaxIdeals
variable {F : Type} [Field F] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_le_of_sup_le_ee37547a7a26 (hD : ChartDehomog.Statement) {W₁ W₂ : Ideal (MvPolynomial (Fin n) F)} {t : Fin n → F}
    (hh₁ : IsHomogIdeal W₁) (h₂ : W₂.IsPrime) (hh₂ : IsHomogIdeal W₂) (ht₂ : linForm t ∉ W₂)
    (h : W₁ ⊔ Ideal.span {linForm t - 1} ≤ W₂ ⊔ Ideal.span {linForm t - 1}) : W₁ ≤ W₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMaxIdeals».«le_of_sup_le» := P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_le_of_sup_le_ee37547a7a26
