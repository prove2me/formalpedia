-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_norm_lterm_diag
-- name    : PositivityTheory.RgJS.DiagonalEntryNormBounds.norm_lterm_diag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:49.847639+00:00
-- url     : https://prove2.me/theorems/f6836951-a383-473c-8c33-87492c607ff5
-- title:
--   Diagonal Entry Norm Bounds: norm lterm diag
-- statement:
--   The Diagonal Entry Norm Bounds construction uses the norm lterm diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/DiagonalTermNorms/ConvergenceOfLandauEuler.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/DiagonalTermNorms/ConvergenceOfLandauEuler.lean#L57-L60

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

theorem PositivityTheory.RgJS.DiagonalEntryNormBounds.norm_lterm_diag {A : Type} [Fintype A] (hq : ∀ w, 2 ≤ q w) (α : W → A → ℂ) (σ : ℝ) (p : W × ℕ) :
    ‖lterm q α α σ p‖ = cd α p * Real.exp (-(ll q p * σ)) := by sorry
