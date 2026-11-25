-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_gaussianInner_monomial_orthogonal
-- name    : ReciprocityTheory.ChartRestriction.G.I2.FPw.gaussianInner_monomial_orthogonal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:32:04.37437+00:00
-- url     : https://prove2.me/theorems/b1c07652-0357-536d-bc76-03168c5cddff
-- title:
--   FPw: gaussian Inner monomial orthogonal
-- statement:
--   The FPw construction uses the gaussian Inner monomial orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaPolyTranslate.lean#L36-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaPolyTranslate.lean#L36-L69

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaPolyTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.FPw.gaussianInner_monomial_orthogonal (q : ℕ) {α β : ι →₀ ℕ} (h : α ≠ β) : paIP q (paMono α) (paMono β) = 0 := by sorry
