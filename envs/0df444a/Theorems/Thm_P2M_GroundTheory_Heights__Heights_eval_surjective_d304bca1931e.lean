-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_surjective_d304bca1931e
-- name    : P2M_GroundTheory_Heights__Heights_eval_surjective_d304bca1931e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:45:52.94373+00:00
-- url     : https://prove2.me/theorems/7a38f7ba-fb40-4121-a71d-4e845f3e2d9a
-- title:
--   P2 M Ground Theory Heights  Heights eval surjective d304bca1931e: P2 M Ground Theory Heights  Heights eval surjective d304bca1931e
-- statement:
--   The P2 M Ground Theory Heights  Heights eval surjective d304bca1931e construction uses the P2 M Ground Theory Heights  Heights eval surjective d304bca1931e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L205-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L205-L206

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

theorem P2M_GroundTheory_Heights__Heights_eval_surjective_d304bca1931e {n : ℕ} (p : Fin n → ℂ) : Function.Surjective (MvPolynomial.eval p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eval_surjective» := P2M_GroundTheory_Heights__Heights_eval_surjective_d304bca1931e
