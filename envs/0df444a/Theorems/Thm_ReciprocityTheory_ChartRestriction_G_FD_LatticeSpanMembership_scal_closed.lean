-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_scal_closed
-- name    : ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.scal_closed
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:19:32.144826+00:00
-- url     : https://prove2.me/theorems/cd4b4315-02a6-401f-9f1c-776e3bf52cc9
-- title:
--   Lattice Span Membership: scal closed
-- statement:
--   The Lattice Span Membership construction uses the scal closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeSpanMembership.lean#L147-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeSpanMembership.lean#L147-L187

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

theorem ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.scal_closed (hD3 : IntegerApproximationCount (E := E)) {ξ : Fin r → E} {w : X.Ψ → Fin r → ℂ}
    (hw : w ∈ Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E)))) (s : X.Ψ → ℂ) :
    (fun τ => s τ • w τ) ∈ Submodule.span ℝ (X.embV '' (X.Λp ξ : Set (Fin r → E))) := by sorry
