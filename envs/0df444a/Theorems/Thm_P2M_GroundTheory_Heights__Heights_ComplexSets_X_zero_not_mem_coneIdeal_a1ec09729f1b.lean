-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_X_zero_not_mem_coneIdeal_a1ec09729f1b
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_X_zero_not_mem_coneIdeal_a1ec09729f1b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:14.635934+00:00
-- url     : https://prove2.me/theorems/91425c6f-6a03-4c9e-8753-9e2107ca1d28
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets X zero not mem cone Ideal a1ec09729f1b: P2 M Ground Theory Heights  Heights Complex Sets X zero not mem cone Ideal a1ec09729f1b
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets X zero not mem cone Ideal a1ec09729f1b construction uses the P2 M Ground Theory Heights  Heights Complex Sets X zero not mem cone Ideal a1ec09729f1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L177-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L177-L189

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_X_zero_not_mem_coneIdeal_a1ec09729f1b : (X 0 : MvPolynomial (Fin 3) ℂ) ∉ coneIdeal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«X_zero_not_mem_coneIdeal» := P2M_GroundTheory_Heights__Heights_ComplexSets_X_zero_not_mem_coneIdeal_a1ec09729f1b
