-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_mem__p_iff_0da98c18e74b
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_mem__p_iff_0da98c18e74b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:19.002104+00:00
-- url     : https://prove2.me/theorems/f2ad89f0-f25a-4a74-8820-c44634708328
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Lattice Span Membership mem  p iff 0da98c18e74b: P2 M Reciprocity Theory Chart Restriction G FD Lattice Span Membership mem  p iff 0da98c18e74b
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Lattice Span Membership mem  p iff 0da98c18e74b construction uses the P2 M Reciprocity Theory Chart Restriction G FD Lattice Span Membership mem  p iff 0da98c18e74b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeSpanMembership.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeSpanMembership.lean#L84-L87

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_mem__p_iff_0da98c18e74b {ξ μ : Fin r → E} : μ ∈ X.Λp ξ ↔ μ ∈ X.Λ ∧ herm X.Gm μ ξ = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«LatticeSpanMembership».«mem_Λp_iff» := P2M_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_mem__p_iff_0da98c18e74b
