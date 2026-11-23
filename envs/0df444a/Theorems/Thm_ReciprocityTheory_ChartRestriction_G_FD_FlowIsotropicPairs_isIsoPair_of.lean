-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowIsotropicPairs_isIsoPair_of
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs.isIsoPair_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:42.823801+00:00
-- url     : https://prove2.me/theorems/da8dd5a7-ca3d-4700-b497-5530119e94d9
-- title:
--   Flow Isotropic Pairs: is Iso Pair of
-- statement:
--   The Flow Isotropic Pairs construction uses the is Iso Pair of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowIsotropicPairs.lean#L42-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowIsotropicPairs.lean#L42-L64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMajorantFlags
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowIsotropicPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs.isIsoPair_of (X : DataX E r) {ξ x : Fin r → E} (hξ : X.IsIso ξ) (hxξ : herm X.Gm x ξ = 0)
    (hxx : herm X.Gm x x = 0) (hne : ∀ e : E, x ≠ e • ξ) :
    IsIsoPair X.Gm ![ξ, (X.NC : E) • x] := by sorry
