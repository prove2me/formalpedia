-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_abs_det_fderiv_real_mul_eq_normSq_b65fe22df9db
-- name    : P2M_GroundTheory_Heights__Heights_abs_det_fderiv_real_mul_eq_normSq_b65fe22df9db
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:43:54.207266+00:00
-- url     : https://prove2.me/theorems/8218f995-8e80-42a5-9d0a-7f435078c0c8
-- title:
--   P2 M Ground Theory Heights  Heights abs det fderiv real mul eq norm Sq b65fe22df9db: P2 M Ground Theory Heights  Heights abs det fderiv real mul eq norm Sq b65fe22df9db
-- statement:
--   The P2 M Ground Theory Heights  Heights abs det fderiv real mul eq norm Sq b65fe22df9db construction uses the P2 M Ground Theory Heights  Heights abs det fderiv real mul eq norm Sq b65fe22df9db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHolomorphicFibreSumInt.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHolomorphicFibreSumInt.lean#L13-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicFibreSumInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeightedAreaFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolomorphicFibreSumInt
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
open MeasureTheory ReciprocityTheory.AnForm.A
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_abs_det_fderiv_real_mul_eq_normSq_b65fe22df9db {d : ℕ} {Ω : Set (Fin d → ℂ)} {τ : (Fin d → ℂ) → Fin d → ℂ}
    (hΩ : IsOpen Ω) (hτ : DifferentiableOn ℂ τ Ω) (H : (Fin d → ℂ) → ℝ) :
    Set.EqOn (fun t => |(fderiv ℝ τ t).det| * H t) (fun t => Complex.normSq (jacC τ t).det * H t) Ω := by sorry

alias «GroundTheory».«Heights₂».«Heights».«abs_det_fderiv_real_mul_eq_normSq» := P2M_GroundTheory_Heights__Heights_abs_det_fderiv_real_mul_eq_normSq_b65fe22df9db
