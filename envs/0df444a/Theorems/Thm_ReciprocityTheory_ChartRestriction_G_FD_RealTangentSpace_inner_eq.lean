-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_inner_eq
-- name    : ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace.inner_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:31:35.005505+00:00
-- url     : https://prove2.me/theorems/bee13834-aeab-47a7-9e0c-30038c04eb5a
-- title:
--   Real Tangent Space: inner eq
-- statement:
--   The Real Tangent Space construction uses the inner eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RealTangentSpace.lean#L96-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RealTangentSpace.lean#L96-L96

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeSpanMembership
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealTangentSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (z : Frame X.Ψ r) (ξ : Fin r → E)
variable [hz : Fact (z ∈ X.dom)]

theorem ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace.inner_eq (u v : VT (X := X) z ξ) : inner ℝ u v = MajorantOperators.gI z u.val v.val := by sorry
