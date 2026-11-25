-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_specFirst_zero_of_isMultiHomog_24c58bee1b93
-- name    : P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_specFirst_zero_of_isMultiHomog_24c58bee1b93
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:17:23.332005+00:00
-- url     : https://prove2.me/theorems/ebc1988f-5410-481f-9244-8315a76501e0
-- title:
--   P2 M Ground Theory Heights  Heights Chart Choice Alg Closed spec First zero of is Multi Homog 24c58bee1b93: P2 M Ground Theory Heights  Heights Chart Choice Alg Closed spec First zero of is Multi Homo
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Choice Alg Closed spec First zero of is Multi Homog 24c58bee1b93 construction uses the P2 M Ground Theory Heights  Heights Chart Choice Alg Closed spec First zero of is Multi Homog 24c58bee1b93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartChoiceAlgClosed.lean#L66-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartChoiceAlgClosed.lean#L66-L87

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

theorem P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_specFirst_zero_of_isMultiHomog_24c58bee1b93 {δ : ℕ} (hδ : 1 ≤ δ) {f : MvPolynomial (Fin (e + 1) × Fin n) F}
    (hf : IsMultiHomog δ f) : specFirst f 0 = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartChoiceAlgClosed».«specFirst_zero_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_ChartChoiceAlgClosed_specFirst_zero_of_isMultiHomog_24c58bee1b93
