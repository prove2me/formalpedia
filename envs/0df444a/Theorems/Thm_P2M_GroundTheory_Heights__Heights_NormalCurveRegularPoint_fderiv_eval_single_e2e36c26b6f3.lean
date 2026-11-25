-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalCurveRegularPoint_fderiv_eval_single_e2e36c26b6f3
-- name    : P2M_GroundTheory_Heights__Heights_NormalCurveRegularPoint_fderiv_eval_single_e2e36c26b6f3
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:49:07.962435+00:00
-- url     : https://prove2.me/theorems/d9cc9060-892f-4e03-8843-0b8bf446faa3
-- title:
--   P2 M Ground Theory Heights  Heights Normal Curve Regular Point fderiv eval single e2e36c26b6f3: P2 M Ground Theory Heights  Heights Normal Curve Regular Point fderiv eval single e2e36c26b6f3
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Curve Regular Point fderiv eval single e2e36c26b6f3 construction uses the P2 M Ground Theory Heights  Heights Normal Curve Regular Point fderiv eval single e2e36c26b6f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalCurveRegularPoint.lean#L15-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalCurveRegularPoint.lean#L15-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveRegularPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveJacobian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalCurveRegularPoint
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
open GroundTheory.Heights₂.Heights.NormalCurveRegularPoint

theorem P2M_GroundTheory_Heights__Heights_NormalCurveRegularPoint_fderiv_eval_single_e2e36c26b6f3 {σ : Type} [Fintype σ] [DecidableEq σ] (g : MvPolynomial σ ℂ) (z : σ → ℂ) (i : σ) :
    fderiv ℂ (fun x : σ → ℂ => eval x g) z (Pi.single i 1) = eval z (pderiv i g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalCurveRegularPoint».«fderiv_eval_single» := P2M_GroundTheory_Heights__Heights_NormalCurveRegularPoint_fderiv_eval_single_e2e36c26b6f3
