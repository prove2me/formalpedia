-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_onb_perp
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis.onb_perp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:19:35.348102+00:00
-- url     : https://prove2.me/theorems/e9fdb585-02b4-428a-9e4b-c96c83017f83
-- title:
--   Orthonormal Perp Basis: onb perp
-- statement:
--   The Orthonormal Perp Basis construction uses the onb perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/OnbPerp.lean#L8-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/OnbPerp.lean#L8-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OnbPerp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
open Complex
open scoped ComplexConjugate InnerProductSpace

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis.onb_perp (n : ℕ) (hn : 1 ≤ n) (α : Fin n → ℂ) (hα : α ≠ 0) :
    ∃ g : Fin (n - 1) → Fin n → ℂ,
      (∀ k l, ∑ a, g k a * conj (g l a) = if k = l then 1 else 0) ∧
      (∀ k, ∑ a, g k a * conj (α a) = 0) ∧
      (∀ γ : Fin n → ℂ, ∑ a, γ a * conj (α a) = 0 → γ ∈ Submodule.span ℂ (Set.range g)) := by sorry
