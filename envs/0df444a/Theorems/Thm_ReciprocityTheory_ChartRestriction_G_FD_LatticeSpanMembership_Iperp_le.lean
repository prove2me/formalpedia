-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_Iperp_le
-- name    : ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.Iperp_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:20:13.463738+00:00
-- url     : https://prove2.me/theorems/78d469a7-66d6-53ec-a2ee-24f4847ee307
-- title:
--   Lattice Span Membership: Iperp le
-- statement:
--   The Lattice Span Membership construction uses the Iperp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeSpanMembership.lean#L189-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeSpanMembership.lean#L189-L261

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeSpanMembership
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.Iperp_le (hD3 : IntegerApproximationCount (E := E)) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    {v : X.Ψ → Fin r → ℂ} (hv : v ∈ X.Iperp ξ) :
    v ∈ Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E))) := by sorry
