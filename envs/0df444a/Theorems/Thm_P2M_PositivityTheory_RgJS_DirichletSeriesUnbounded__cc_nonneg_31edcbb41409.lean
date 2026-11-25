-- Prove2me | Theorems.Thm_P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__cc_nonneg_31edcbb41409
-- name    : P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__cc_nonneg_31edcbb41409
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:02:36.748257+00:00
-- url     : https://prove2.me/theorems/c593c082-5c70-4e22-9449-77ab82c83d41
-- title:
--   P2 M Positivity Theory Rg JS Dirichlet Series Unbounded  cc nonneg 31edcbb41409: P2 M Positivity Theory Rg JS Dirichlet Series Unbounded  cc nonneg 31edcbb41409
-- statement:
--   The P2 M Positivity Theory Rg JS Dirichlet Series Unbounded  cc nonneg 31edcbb41409 construction uses the P2 M Positivity Theory Rg JS Dirichlet Series Unbounded  cc nonneg 31edcbb41409 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/NonnegativeCoefficients/DirichletSeriesUnbounded.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/NonnegativeCoefficients/DirichletSeriesUnbounded.lean#L19-L20

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

theorem P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__cc_nonneg_31edcbb41409 (p : W × ℕ) : 0 ≤ cc A x p := by sorry

alias «PositivityTheory».«RgJS».«DirichletSeriesUnbounded₂».«cc_nonneg» := P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__cc_nonneg_31edcbb41409
