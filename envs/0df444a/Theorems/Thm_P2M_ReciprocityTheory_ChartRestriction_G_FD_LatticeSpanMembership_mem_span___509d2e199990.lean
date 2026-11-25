-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_mem_span___509d2e199990
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_mem_span___509d2e199990
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:58.959811+00:00
-- url     : https://prove2.me/theorems/cd1044da-e4be-5f72-8823-0ee850c69306
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Lattice Span Membership mem span   509d2e199990: P2 M Reciprocity Theory Chart Restriction G FD Lattice Span Membership mem span   509d2e199990
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Lattice Span Membership mem span   509d2e199990 construction uses the P2 M Reciprocity Theory Chart Restriction G FD Lattice Span Membership mem span   509d2e199990 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeSpanMembership.lean#L108-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeSpanMembership.lean#L108-L145

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_mem_span___509d2e199990 (hD3 : IntegerApproximationCount (E := E)) (v : X.Ψ → Fin r → ℂ) :
    v ∈ Submodule.span ℝ (X.embV '' (X.Λ : Set (Fin r → E))) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«LatticeSpanMembership».«mem_span_Λ» := P2M_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_mem_span___509d2e199990
