-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FixedPointImaginarySpan_im_of_fixed
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan.im_of_fixed
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:13:12.612871+00:00
-- url     : https://prove2.me/theorems/14ffee7f-e501-5531-91e2-4bba15207956
-- title:
--   Fixed Point Imaginary Span: im of fixed
-- statement:
--   The Fixed Point Imaginary Span construction uses the im of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FixedPointImaginarySpan.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FixedPointImaginarySpan.lean#L15-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FixedPointImaginarySpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
  ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (g : ℕ)

theorem ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan.im_of_fixed {a : E} (ha : cc a = a) (τ : E →+* ℂ) : (τ a).im = 0 := by sorry
