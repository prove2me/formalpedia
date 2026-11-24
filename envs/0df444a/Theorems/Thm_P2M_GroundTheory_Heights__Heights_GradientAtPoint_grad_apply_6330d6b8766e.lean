-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_apply_6330d6b8766e
-- name    : P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_apply_6330d6b8766e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:17.103538+00:00
-- url     : https://prove2.me/theorems/3d13a130-327b-432a-830f-025c14e3c37e
-- title:
--   P2 M Ground Theory Heights  Heights Gradient At Point grad apply 6330d6b8766e: P2 M Ground Theory Heights  Heights Gradient At Point grad apply 6330d6b8766e
-- statement:
--   The P2 M Ground Theory Heights  Heights Gradient At Point grad apply 6330d6b8766e construction uses the P2 M Ground Theory Heights  Heights Gradient At Point grad apply 6330d6b8766e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L17-L18

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

theorem P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_apply_6330d6b8766e (p : MvPolynomial σ ℂ) (i : σ) : grad w p i = eval w (pderiv i p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradientAtPoint».«grad_apply» := P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_apply_6330d6b8766e
