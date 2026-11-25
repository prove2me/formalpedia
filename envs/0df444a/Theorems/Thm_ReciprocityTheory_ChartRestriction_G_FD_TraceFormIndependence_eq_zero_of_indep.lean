-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceFormIndependence_eq_zero_of_indep
-- name    : ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence.eq_zero_of_indep
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:14:45.970366+00:00
-- url     : https://prove2.me/theorems/1f96a6c3-9d74-49e5-b32f-effc2bf79037
-- title:
--   Trace Form Independence: eq zero of indep
-- statement:
--   The Trace Form Independence construction uses the eq zero of indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TraceFormIndependence.lean#L124-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TraceFormIndependence.lean#L124-L190

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceFormIndependence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.TraceFormIndependence.eq_zero_of_indep (X : Data E r) (d : X.Ψ → ℂ)
    (h : ∀ β : 𝓞 E, ∑ τ : X.Ψ, 2 * (d τ * conj (τ.1 (β : E))).re = 0) (τ0 : X.Ψ) :
    d τ0 = 0 := by sorry
