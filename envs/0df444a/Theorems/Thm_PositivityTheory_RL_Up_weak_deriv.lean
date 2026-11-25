-- Prove2me | Theorems.Thm_PositivityTheory_RL_Up_weak_deriv
-- name    : PositivityTheory.RL.Up.weak_deriv
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:01.262544+00:00
-- url     : https://prove2.me/theorems/fdc99356-8f01-4592-adb2-63102699e64c
-- title:
--   Up: weak deriv
-- statement:
--   The Up construction uses the weak deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieA.lean#L197-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieA.lean#L197-L253

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix Filter Topology Asymptotics
open scoped Real RealInnerProductSpace ContDiff
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Up
open GlobalTheory.RealWeil
variable {l : Type} [Fintype l] [DecidableEq l]

theorem PositivityTheory.RL.Up.weak_deriv (U : ℝ → (Sch l →L[ℂ] Sch l)) (Q : Sch l →L[ℂ] Sch l) (h0 : U 0 = 1)
    (hj : Good U Q (toBoundedContinuousFunctionCLM ℂ _ ℂ))
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (c : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ))
    (hc0 : ∀ w, c 0 w = w) (hc : ∀ w a, HasDerivAt (fun t => c t w a) (-(X *ᵥ w) a) 0)
    (hD : ∀ t w, dRho w * U t = U t * dRho (c t w))
    (hQ : ∀ w, Q * dRho w - dRho w * Q = dRho (X *ᵥ w)) (T : Sch l →L[ℂ] ℂ) : Good U Q T := by sorry
