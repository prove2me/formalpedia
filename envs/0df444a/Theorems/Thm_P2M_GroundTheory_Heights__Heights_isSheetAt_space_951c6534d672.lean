-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isSheetAt_space_951c6534d672
-- name    : P2M_GroundTheory_Heights__Heights_isSheetAt_space_951c6534d672
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:41:24.193834+00:00
-- url     : https://prove2.me/theorems/83640c27-6079-4b1d-a5c5-5e49208631f0
-- title:
--   P2 M Ground Theory Heights  Heights is Sheet At space 951c6534d672: P2 M Ground Theory Heights  Heights is Sheet At space 951c6534d672
-- statement:
--   The P2 M Ground Theory Heights  Heights is Sheet At space 951c6534d672 construction uses the P2 M Ground Theory Heights  Heights is Sheet At space 951c6534d672 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L257-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L257-L264

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_isSheetAt_space_951c6534d672 {n : ℕ} (x : Fin n → ℂ) :
    IsSheetAt (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ) x id := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isSheetAt_space» := P2M_GroundTheory_Heights__Heights_isSheetAt_space_951c6534d672
