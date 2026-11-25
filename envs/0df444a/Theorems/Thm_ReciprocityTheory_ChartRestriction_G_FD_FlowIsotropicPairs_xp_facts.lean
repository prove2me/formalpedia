-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowIsotropicPairs_xp_facts
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs.xp_facts
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:14:11.039718+00:00
-- url     : https://prove2.me/theorems/3e2d838b-f0ef-5a19-97c3-a6db69291e6f
-- title:
--   Flow Isotropic Pairs: xp facts
-- statement:
--   The Flow Isotropic Pairs construction uses the xp facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowIsotropicPairs.lean#L74-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowIsotropicPairs.lean#L74-L99

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

theorem ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs.xp_facts (X : Data E r) {ξ x : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0) (hξ0 : ξ ≠ 0)
    (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.dom)
    (τ : X.Ψ) :
    hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV x) τ) (Data.emb τ.1 ξ) = 0 ∧
      hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV x) τ) (X.ucomp z0 ξ (X.embV x) τ) = 0 ∧
      X.Hf z0 τ (X.ucomp z0 ξ (X.embV x) τ) (Data.emb τ.1 ξ) = 0 := by sorry
