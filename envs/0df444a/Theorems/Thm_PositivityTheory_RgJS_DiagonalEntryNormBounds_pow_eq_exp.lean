-- Prove2me | Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_pow_eq_exp
-- name    : PositivityTheory.RgJS.DiagonalEntryNormBounds.pow_eq_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:01.631156+00:00
-- url     : https://prove2.me/theorems/4d7c65cf-9da0-4868-823d-366916fe1895
-- title:
--   Diagonal Entry Norm Bounds: pow eq exp
-- statement:
--   The Diagonal Entry Norm Bounds construction uses the pow eq exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/DiagonalTermNorms/ConvergenceOfLandauEuler.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/DiagonalTermNorms/ConvergenceOfLandauEuler.lean#L20-L27

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

theorem PositivityTheory.RgJS.DiagonalEntryNormBounds.pow_eq_exp (hq : ∀ w, 2 ≤ q w) (σ : ℝ) (p : W × ℕ) :
    ((q p.1 : ℝ) ^ (-σ)) ^ (p.2 + 1) = Real.exp (-(ll q p * σ)) := by sorry
