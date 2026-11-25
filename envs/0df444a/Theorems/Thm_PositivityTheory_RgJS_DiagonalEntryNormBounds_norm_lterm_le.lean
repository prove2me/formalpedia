-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_norm_lterm_le
-- name    : PositivityTheory.RgJS.DiagonalEntryNormBounds.norm_lterm_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:03:03.512949+00:00
-- url     : https://prove2.me/theorems/1056e2cc-8253-480d-9616-80f7ef5d8e29
-- title:
--   Diagonal Entry Norm Bounds: norm lterm le
-- statement:
--   The Diagonal Entry Norm Bounds construction uses the norm lterm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/DiagonalTermNorms/ConvergenceOfLandauEuler.lean#L62-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/DiagonalTermNorms/ConvergenceOfLandauEuler.lean#L62-L77

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_DiagonalTermNorms_ConvergenceOfLandauEuler
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.RgJS
open PositivityTheory.RgJS.DiagonalEntryNormBounds
variable {W : Type} (q : W → ℕ)

theorem PositivityTheory.RgJS.DiagonalEntryNormBounds.norm_lterm_le {A B : Type} [Fintype A] [Fintype B] (hq : ∀ w, 2 ≤ q w) (α : W → A → ℂ) (β : W → B → ℂ)
    (σ : ℝ) (p : W × ℕ) :
    ‖lterm q α β σ p‖ ≤ (‖lterm q α α σ p‖ + ‖lterm q β β σ p‖) / 2 := by sorry
