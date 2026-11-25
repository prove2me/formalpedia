-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeSpanMembership_Uz_le_span
-- name    : ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.Uz_le_span
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:20:03.464063+00:00
-- url     : https://prove2.me/theorems/aad7c161-c096-50a4-a9c5-5abfcd8f4328
-- title:
--   Lattice Span Membership: Uz le span
-- statement:
--   The Lattice Span Membership construction uses the Uz le span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeSpanMembership.lean#L263-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LatticeSpanMembership.lean#L263-L291

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

theorem ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.Uz_le_span (hD3 : IntegerApproximationCount (E := E)) {z : Frame X.Ψ r} {ξ : Fin r → E}
    (hξ : X.IsIso ξ) {u : X.Ψ → Fin r → ℂ} (hu : u ∈ X.Uz z ξ) :
    u ∈ Submodule.span ℝ (Set.range fun μ : X.Λp ξ => X.ucomp z ξ (X.embV μ)) := by sorry
