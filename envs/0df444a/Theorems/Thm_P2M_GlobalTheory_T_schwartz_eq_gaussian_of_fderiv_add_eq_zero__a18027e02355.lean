-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_schwartz_eq_gaussian_of_fderiv_add_eq_zero__a18027e02355
-- name    : P2M_GlobalTheory_T_schwartz_eq_gaussian_of_fderiv_add_eq_zero__a18027e02355
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:06:26.186113+00:00
-- url     : https://prove2.me/theorems/9ce70518-a3dc-4128-ad01-a1905c9fd883
-- title:
--   P2 M Global Theory T schwartz eq gaussian of fderiv add eq zero  a18027e02355: P2 M Global Theory T schwartz eq gaussian of fderiv add eq zero  a18027e02355
-- statement:
--   The P2 M Global Theory T schwartz eq gaussian of fderiv add eq zero  a18027e02355 construction uses the P2 M Global Theory T schwartz eq gaussian of fderiv add eq zero  a18027e02355 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzEqGaussianOfFderivAddEqZeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzEqGaussianOfFderivAddEqZeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzEqGaussianOfFderivAddEqZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzEqGaussianOfFderivAddEqZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_schwartz_eq_gaussian_of_fderiv_add_eq_zero__a18027e02355 : ∀ (l : Type) [Fintype l] [DecidableEq l] (h : 𝓢(EuclideanSpace ℝ l, ℂ)), (∀ (j : l) (x : EuclideanSpace ℝ l), fderiv ℝ (⇑h) x (EuclideanSpace.single j 1) + 2 * Real.pi * (x j : ℂ) * h x = 0) → ∀ x, h x = h 0 * ((Real.exp (-Real.pi * ‖x‖ ^ 2) : ℝ) : ℂ) := by sorry

alias «GlobalTheory».«T».«schwartz_eq_gaussian_of_fderiv_add_eq_zero'» := P2M_GlobalTheory_T_schwartz_eq_gaussian_of_fderiv_add_eq_zero__a18027e02355
