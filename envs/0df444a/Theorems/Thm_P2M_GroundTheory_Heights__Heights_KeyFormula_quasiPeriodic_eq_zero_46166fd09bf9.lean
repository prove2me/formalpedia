-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_quasiPeriodic_eq_zero_46166fd09bf9
-- name    : P2M_GroundTheory_Heights__Heights_KeyFormula_quasiPeriodic_eq_zero_46166fd09bf9
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:26:14.791995+00:00
-- url     : https://prove2.me/theorems/4af7f3ac-1d6a-465f-901c-b102f3ba255a
-- title:
--   P2 M Ground Theory Heights  Heights Key Formula quasi Periodic eq zero 46166fd09bf9: P2 M Ground Theory Heights  Heights Key Formula quasi Periodic eq zero 46166fd09bf9
-- statement:
--   The P2 M Ground Theory Heights  Heights Key Formula quasi Periodic eq zero 46166fd09bf9 construction uses the P2 M Ground Theory Heights  Heights Key Formula quasi Periodic eq zero 46166fd09bf9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/ThetaThreeFamLinearIndependent.lean#L49-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ThetaKeyFormula/ThetaThreeFamLinearIndependent.lean#L49-L137

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Real MeasureTheory intervalIntegral Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_KeyFormula_quasiPeriodic_eq_zero_46166fd09bf9 (n : ℕ) (hn : 0 < n) (h : ℂ → ℂ) (hd : Differentiable ℂ h) (C : ℂ)
    (hC : C ≠ 0) (h1 : ∀ w, h (w + 1) = h w)
    (h2 : ∀ w, h (w + I) = C * cexp (-2 * π * I * n * w) * h w)
    (h0 : ∀ k : ℕ, k < n → ∫ x in (0 : ℝ)..1, h x * cexp (-2 * π * I * k * x) = 0) : h = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KeyFormula».«quasiPeriodic_eq_zero» := P2M_GroundTheory_Heights__Heights_KeyFormula_quasiPeriodic_eq_zero_46166fd09bf9
