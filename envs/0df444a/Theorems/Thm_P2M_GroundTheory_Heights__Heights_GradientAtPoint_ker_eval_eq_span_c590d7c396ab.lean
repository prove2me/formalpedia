-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_ker_eval_eq_span_c590d7c396ab
-- name    : P2M_GroundTheory_Heights__Heights_GradientAtPoint_ker_eval_eq_span_c590d7c396ab
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:03.260813+00:00
-- url     : https://prove2.me/theorems/dc9290d1-39a0-4f85-b95f-f818bab79254
-- title:
--   P2 M Ground Theory Heights  Heights Gradient At Point ker eval eq span c590d7c396ab: P2 M Ground Theory Heights  Heights Gradient At Point ker eval eq span c590d7c396ab
-- statement:
--   The P2 M Ground Theory Heights  Heights Gradient At Point ker eval eq span c590d7c396ab construction uses the P2 M Ground Theory Heights  Heights Gradient At Point ker eval eq span c590d7c396ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L72-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L72-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
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
open GroundTheory.Heights₂.Heights.GradientAtPoint
variable {σ : Type*} (w : σ → ℂ)

theorem P2M_GroundTheory_Heights__Heights_GradientAtPoint_ker_eval_eq_span_c590d7c396ab :
    RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) =
      Ideal.span (Set.range fun i => (X i - C (w i) : MvPolynomial σ ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradientAtPoint».«ker_eval_eq_span» := P2M_GroundTheory_Heights__Heights_GradientAtPoint_ker_eval_eq_span_c590d7c396ab
