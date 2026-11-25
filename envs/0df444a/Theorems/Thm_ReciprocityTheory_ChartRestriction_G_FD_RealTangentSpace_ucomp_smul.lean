-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealTangentSpace_ucomp_smul
-- name    : ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace.ucomp_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:31:46.528737+00:00
-- url     : https://prove2.me/theorems/36c066c4-e0c2-4e83-8222-07073a9d876e
-- title:
--   Real Tangent Space: ucomp smul
-- statement:
--   The Real Tangent Space construction uses the ucomp smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RealTangentSpace.lean#L120-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RealTangentSpace.lean#L120-L131

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
omit hz

theorem ReciprocityTheory.ChartRestriction.G.FD.RealTangentSpace.ucomp_smul (a : ℝ) (u : X.Ψ → Fin r → ℂ) : X.ucomp z ξ (a • u) = a • X.ucomp z ξ u := by sorry
