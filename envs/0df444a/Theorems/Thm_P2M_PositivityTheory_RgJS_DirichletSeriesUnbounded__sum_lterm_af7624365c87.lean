-- Prove2me | Theorems.Thm_P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__sum_lterm_af7624365c87
-- name    : P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__sum_lterm_af7624365c87
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:02:12.972594+00:00
-- url     : https://prove2.me/theorems/63059441-4d37-46b9-8d41-1a9c8096d0af
-- title:
--   P2 M Positivity Theory Rg JS Dirichlet Series Unbounded  sum lterm af7624365c87: P2 M Positivity Theory Rg JS Dirichlet Series Unbounded  sum lterm af7624365c87
-- statement:
--   The P2 M Positivity Theory Rg JS Dirichlet Series Unbounded  sum lterm af7624365c87 construction uses the P2 M Positivity Theory Rg JS Dirichlet Series Unbounded  sum lterm af7624365c87 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/NonnegativeCoefficients/DirichletSeriesUnbounded.lean#L33-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/NonnegativeCoefficients/DirichletSeriesUnbounded.lean#L33-L49

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

theorem P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__sum_lterm_af7624365c87 (hq : ∀ w, (0 : ℝ) < q w) (σ : ℝ) (p : W × ℕ) :
    ∑ i, ∑ j, lterm q (A (x i)) (A (x j)) σ p = ((cc A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by sorry

alias «PositivityTheory».«RgJS».«DirichletSeriesUnbounded₂».«sum_lterm» := P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__sum_lterm_af7624365c87
