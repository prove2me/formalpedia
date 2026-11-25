-- Prove2me | Theorems.Thm_PI_FdFjNearSup_W_spread_nonneg
-- name    : PI.FdFjNearSup.W.spread_nonneg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:04.350656+00:00
-- url     : https://prove2.me/theorems/ae81f248-f55d-4d38-88ae-f6ad6536b376
-- title:
--   W: spread nonneg
-- statement:
--   The W construction uses the spread nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSupOf.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSupOf.lean#L57-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_NearSupremumBounds_FdFjNearSupOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FdFjNearSup PI.FdFjNearSup.W
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex MeasureTheory
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem PI.FdFjNearSup.W.spread_nonneg {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (τ : X.Ψ) : 0 ≤ X.spread la τ := by sorry
