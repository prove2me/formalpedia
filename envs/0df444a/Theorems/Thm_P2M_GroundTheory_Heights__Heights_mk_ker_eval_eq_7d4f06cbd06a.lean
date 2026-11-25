-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mk_ker_eval_eq_7d4f06cbd06a
-- name    : P2M_GroundTheory_Heights__Heights_mk_ker_eval_eq_7d4f06cbd06a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:07.218439+00:00
-- url     : https://prove2.me/theorems/0be358b2-f1ad-498d-8d60-bd1f417c76d0
-- title:
--   P2 M Ground Theory Heights  Heights mk ker eval eq 7d4f06cbd06a: P2 M Ground Theory Heights  Heights mk ker eval eq 7d4f06cbd06a
-- statement:
--   The P2 M Ground Theory Heights  Heights mk ker eval eq 7d4f06cbd06a construction uses the P2 M Ground Theory Heights  Heights mk ker eval eq 7d4f06cbd06a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L199-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StatementsCurrent.lean#L199-L203

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

theorem P2M_GroundTheory_Heights__Heights_mk_ker_eval_eq_7d4f06cbd06a {n : ℕ} (p : Fin n → ℂ) (q : MvPolynomial (Fin n) ℂ) :
    Ideal.Quotient.mk (RingHom.ker (MvPolynomial.eval p)) q =
      algebraMap ℂ _ (MvPolynomial.eval p q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mk_ker_eval_eq» := P2M_GroundTheory_Heights__Heights_mk_ker_eval_eq_7d4f06cbd06a
