-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_smul_int_mem
-- name    : ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.smul_int_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:38.064046+00:00
-- url     : https://prove2.me/theorems/6cd793d2-85e4-4126-9047-d9d81aa19b7e
-- title:
--   Lattice Span Membership: smul int mem
-- statement:
--   The Lattice Span Membership construction uses the smul int mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeSpanMembership.lean#L89-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeSpanMembership.lean#L89-L94

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

theorem ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.smul_int_mem {α : E} (hα : IsIntegral ℤ α) {v : Fin r → E} (hv : v ∈ X.Λ) : α • v ∈ X.Λ := by sorry
