-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_lterm_diag
-- name    : PositivityTheory.RgJS.DiagonalEntryNormBounds.lterm_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:57.918287+00:00
-- url     : https://prove2.me/theorems/654e1d58-9936-4596-b802-2fb87324de76
-- title:
--   Diagonal Entry Norm Bounds: lterm diag
-- statement:
--   The Diagonal Entry Norm Bounds construction uses the lterm diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/DiagonalTermNorms/ConvergenceOfLandauEuler.lean#L47-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/DiagonalTermNorms/ConvergenceOfLandauEuler.lean#L47-L55

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

theorem PositivityTheory.RgJS.DiagonalEntryNormBounds.lterm_diag {A : Type} [Fintype A] (hq : ∀ w, 2 ≤ q w) (α : W → A → ℂ) (σ : ℝ) (p : W × ℕ) :
    lterm q α α σ p = ((cd α p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by sorry
