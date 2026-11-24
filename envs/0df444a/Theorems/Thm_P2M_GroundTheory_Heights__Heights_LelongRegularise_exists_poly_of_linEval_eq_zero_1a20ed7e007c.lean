-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_exists_poly_of_linEval_eq_zero_1a20ed7e007c
-- name    : P2M_GroundTheory_Heights__Heights_LelongRegularise_exists_poly_of_linEval_eq_zero_1a20ed7e007c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:05.08011+00:00
-- url     : https://prove2.me/theorems/43cfcf2b-6140-4cc0-bcce-24225273ad58
-- title:
--   P2 M Ground Theory Heights  Heights Lelong Regularise exists poly of lin Eval eq zero 1a20ed7e007c: P2 M Ground Theory Heights  Heights Lelong Regularise exists poly of lin Eval eq zero 1a20ed7e007c
-- statement:
--   The P2 M Ground Theory Heights  Heights Lelong Regularise exists poly of lin Eval eq zero 1a20ed7e007c construction uses the P2 M Ground Theory Heights  Heights Lelong Regularise exists poly of lin Eval eq zero 1a20ed7e007c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongRegularise.lean#L88-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLelongRegularise.lean#L88-L120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
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
open GroundTheory.Heights₂.Heights.LelongRegularise

theorem P2M_GroundTheory_Heights__Heights_LelongRegularise_exists_poly_of_linEval_eq_zero_1a20ed7e007c {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} {u : Fin n → ℂ} (hJ : J.IsPrime) (hA : IsFiniteProjection J A)
    (hu : linForm u ∉ J) :
    ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧
      ∀ y x, x ∈ fibre J A y → linEval u x = 0 → MvPolynomial.eval y P = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LelongRegularise».«exists_poly_of_linEval_eq_zero» := P2M_GroundTheory_Heights__Heights_LelongRegularise_exists_poly_of_linEval_eq_zero_1a20ed7e007c
