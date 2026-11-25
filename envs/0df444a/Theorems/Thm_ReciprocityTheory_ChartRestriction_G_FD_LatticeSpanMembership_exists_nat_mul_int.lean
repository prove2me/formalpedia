-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_exists_nat_mul_int
-- name    : ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.exists_nat_mul_int
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:19:13.594725+00:00
-- url     : https://prove2.me/theorems/1bf55e57-e2fd-405d-9858-8b02d8fc7233
-- title:
--   Lattice Span Membership: exists nat mul int
-- statement:
--   The Lattice Span Membership construction uses the exists nat mul int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeSpanMembership.lean#L44-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeSpanMembership.lean#L44-L54

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

theorem ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.exists_nat_mul_int (c : E) : ∃ N : ℕ, 0 < N ∧ IsIntegral ℤ ((N : E) * c) := by sorry
