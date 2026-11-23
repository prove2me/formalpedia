-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_norm_lterm
-- name    : PositivityTheory.RgJS.DiagonalEntryNormBounds.norm_lterm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:03.701338+00:00
-- url     : https://prove2.me/theorems/4c984344-c070-4049-9b51-d413fb632e26
-- title:
--   Diagonal Entry Norm Bounds: norm lterm
-- statement:
--   The Diagonal Entry Norm Bounds construction uses the norm lterm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/DiagonalTermNorms/ConvergenceOfLandauEuler.lean#L29-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/DiagonalTermNorms/ConvergenceOfLandauEuler.lean#L29-L40

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

theorem PositivityTheory.RgJS.DiagonalEntryNormBounds.norm_lterm {A B : Type} [Fintype A] [Fintype B] (hq : ∀ w, 2 ≤ q w) (α : W → A → ℂ) (β : W → B → ℂ) (σ : ℝ)
    (p : W × ℕ) :
    ‖lterm q α β σ p‖ = ‖∑ a, α p.1 a ^ (p.2 + 1)‖ * ‖∑ b, β p.1 b ^ (p.2 + 1)‖ * Real.exp (-(ll q p * σ)) /
      ((p.2 : ℝ) + 1) := by sorry
