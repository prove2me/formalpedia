-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_mul_206fa499c46e
-- name    : P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_mul_206fa499c46e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:56.436169+00:00
-- url     : https://prove2.me/theorems/f5ac99d5-dc86-46e7-84df-7bcc8054c944
-- title:
--   P2 M Ground Theory Heights  Heights Gradient At Point grad mul 206fa499c46e: P2 M Ground Theory Heights  Heights Gradient At Point grad mul 206fa499c46e
-- statement:
--   The P2 M Ground Theory Heights  Heights Gradient At Point grad mul 206fa499c46e construction uses the P2 M Ground Theory Heights  Heights Gradient At Point grad mul 206fa499c46e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L20-L23

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

theorem P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_mul_206fa499c46e (a b : MvPolynomial σ ℂ) :
    grad w (a * b) = eval w a • grad w b + eval w b • grad w a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradientAtPoint».«grad_mul» := P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_mul_206fa499c46e
