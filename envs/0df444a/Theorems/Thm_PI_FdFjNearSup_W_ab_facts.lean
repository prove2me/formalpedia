-- Prove2me | Theorems.Thm_PI_FdFjNearSup_W_ab_facts
-- name    : PI.FdFjNearSup.W.ab_facts
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:28.553485+00:00
-- url     : https://prove2.me/theorems/f345e0fe-f343-44fe-a85b-2cbc35b2ef81
-- title:
--   W: ab facts
-- statement:
--   The W construction uses the ab facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSupOf.lean#L140-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSupOf.lean#L140-L151

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

theorem PI.FdFjNearSup.W.ab_facts {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1 / 36) :
    0 < (1 - ρ) / (1 + ρ) ∧ ((1 - ρ) / (1 + ρ))⁻¹ = (1 + ρ) / (1 - ρ) ∧
      1 - 2 * ρ ≤ (1 - ρ) / (1 + ρ) ∧ (1 + ρ) / (1 - ρ) ≤ 1 + 3 * ρ ∧ 1 ≤ (1 + ρ) / (1 - ρ) := by sorry
