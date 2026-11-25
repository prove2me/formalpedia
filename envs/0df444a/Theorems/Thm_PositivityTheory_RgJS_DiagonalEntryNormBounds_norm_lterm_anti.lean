-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_norm_lterm_anti
-- name    : PositivityTheory.RgJS.DiagonalEntryNormBounds.norm_lterm_anti
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:03:06.947825+00:00
-- url     : https://prove2.me/theorems/35bdd064-2079-5a03-89b4-9b1a5da6f9b4
-- title:
--   Diagonal Entry Norm Bounds: norm lterm anti
-- statement:
--   The Diagonal Entry Norm Bounds construction uses the norm lterm anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/DiagonalTermNorms/ConvergenceOfLandauEuler.lean#L79-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/DiagonalTermNorms/ConvergenceOfLandauEuler.lean#L79-L87

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

theorem PositivityTheory.RgJS.DiagonalEntryNormBounds.norm_lterm_anti {A B : Type} [Fintype A] [Fintype B] (hq : ∀ w, 2 ≤ q w) (α : W → A → ℂ) (β : W → B → ℂ)
    {σ σ₁ : ℝ} (h : σ₁ ≤ σ) (p : W × ℕ) : ‖lterm q α β σ p‖ ≤ ‖lterm q α β σ₁ p‖ := by sorry
