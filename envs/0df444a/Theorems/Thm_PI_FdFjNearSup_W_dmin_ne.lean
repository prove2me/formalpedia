-- Prove2me | Theorems.Thm_PI_FdFjNearSup_W_dmin_ne
-- name    : PI.FdFjNearSup.W.dmin_ne
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:28.605645+00:00
-- url     : https://prove2.me/theorems/300c077f-15a7-4e9b-a06b-9b20070595b0
-- title:
--   W: dmin ne
-- statement:
--   The W construction uses the dmin ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSupOf.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSupOf.lean#L35-L41

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

theorem PI.FdFjNearSup.W.dmin_ne {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ)
    (j : Fin (r + 1)) : dmin X.Gm x τ j ≠ 0 := by sorry
