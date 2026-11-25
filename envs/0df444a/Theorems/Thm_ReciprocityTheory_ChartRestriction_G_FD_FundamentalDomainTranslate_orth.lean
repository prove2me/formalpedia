-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FundamentalDomainTranslate_orth
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate.orth
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:17:33.619532+00:00
-- url     : https://prove2.me/theorems/acf217b3-e9d5-598f-ae4a-0c7ef318db18
-- title:
--   Fundamental Domain Translate: orth
-- statement:
--   The Fundamental Domain Translate construction uses the orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainTranslate.lean#L22-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainTranslate.lean#L22-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate
open MeasureTheory Complex
open scoped Pointwise
variable {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate.orth (L : AddSubgroup (ι → ℝ)) [Countable L] (D : Set (ι → ℝ))
    (hD : IsAddFundamentalDomain L D volume) (μ : ι → ℝ) (hμ : ∀ p ∈ L, ∃ k : ℤ, 2 * ∑ i, μ i * p i = k) :
    ∫ s in D, cexp (4 * Real.pi * I * ∑ i, (μ i : ℂ) * s i) =
      if μ = 0 then ((volume D).toReal : ℂ) else 0 := by sorry
