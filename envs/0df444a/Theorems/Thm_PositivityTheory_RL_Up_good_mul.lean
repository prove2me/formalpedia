-- Prove2me | Theorems.Thm_PositivityTheory_RL_Up_good_mul
-- name    : PositivityTheory.RL.Up.good_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:51:53.636671+00:00
-- url     : https://prove2.me/theorems/21d162ed-24f0-5a18-8c4c-57cedd3165fa
-- title:
--   Up: good mul
-- statement:
--   The Up construction uses the good mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieA.lean#L124-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieA.lean#L124-L144

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

theorem PositivityTheory.RL.Up.good_mul {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (U : ℝ → (Sch l →L[ℂ] Sch l))
    (Q : Sch l →L[ℂ] Sch l) (h0 : U 0 = 1) (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (c : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ))
    (hc0 : ∀ w, c 0 w = w) (hc : ∀ w a, HasDerivAt (fun t => c t w a) (-(X *ᵥ w) a) 0)
    (hD : ∀ t w, dRho w * U t = U t * dRho (c t w))
    (hQ : ∀ w, Q * dRho w - dRho w * Q = dRho (X *ᵥ w)) {j : Sch l →L[ℂ] B} (hj : Good U Q j) (w : l ⊕ l → ℝ) :
    Good U Q (j ∘L dRho w) := by sorry
