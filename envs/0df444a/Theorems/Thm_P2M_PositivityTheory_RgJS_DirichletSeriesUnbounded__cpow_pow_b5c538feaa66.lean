-- Prove2me | Theorems.Thm_P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__cpow_pow_b5c538feaa66
-- name    : P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__cpow_pow_b5c538feaa66
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:02:01.435632+00:00
-- url     : https://prove2.me/theorems/299da38e-86c2-5496-a94e-5fa4a76d7653
-- title:
--   P2 M Positivity Theory Rg JS Dirichlet Series Unbounded  cpow pow b5c538feaa66: P2 M Positivity Theory Rg JS Dirichlet Series Unbounded  cpow pow b5c538feaa66
-- statement:
--   The P2 M Positivity Theory Rg JS Dirichlet Series Unbounded  cpow pow b5c538feaa66 construction uses the P2 M Positivity Theory Rg JS Dirichlet Series Unbounded  cpow pow b5c538feaa66 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/NonnegativeCoefficients/DirichletSeriesUnbounded.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/NonnegativeCoefficients/DirichletSeriesUnbounded.lean#L22-L31

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NonnegativeCoefficients_DirichletSeriesUnbounded
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
open PositivityTheory.RgJS.DirichletSeriesUnbounded₂
variable {W X : Type} (q : W → ℕ) {d : X → ℕ} (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι] (x : ι → X)

theorem P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__cpow_pow_b5c538feaa66 (hq : ∀ w, (0 : ℝ) < q w) (σ : ℝ) (p : W × ℕ) :
    ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) = ((Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by sorry

alias «PositivityTheory».«RgJS».«DirichletSeriesUnbounded₂».«cpow_pow» := P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__cpow_pow_b5c538feaa66
