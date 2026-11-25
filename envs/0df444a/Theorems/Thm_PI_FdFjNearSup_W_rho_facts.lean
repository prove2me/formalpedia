-- Prove2me | Theorems.Thm_PI_FdFjNearSup_W_rho_facts
-- name    : PI.FdFjNearSup.W.rho_facts
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:30:00.26341+00:00
-- url     : https://prove2.me/theorems/d909a594-4993-45b4-9b33-47ce6c00a9fa
-- title:
--   W: rho facts
-- statement:
--   The W construction uses the rho facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSupOf.lean#L128-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSupOf.lean#L128-L138

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

theorem PI.FdFjNearSup.W.rho_facts {c1 w : ℝ} (hc1 : 0 < c1) (hw : 1 ≤ w) :
    0 < d6rh c1 w ∧ d6rh c1 w ≤ 1 / 36 ∧ 12 * Real.pi * (c1 + w) * d6rh c1 w = 1 := by sorry
