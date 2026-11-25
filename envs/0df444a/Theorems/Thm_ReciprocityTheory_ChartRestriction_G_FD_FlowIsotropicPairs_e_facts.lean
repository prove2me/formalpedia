-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowIsotropicPairs_e_facts
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs.e_facts
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:13:46.034806+00:00
-- url     : https://prove2.me/theorems/6a42cfb2-a7e4-5c91-afdb-c2cd0806e28b
-- title:
--   Flow Isotropic Pairs: e facts
-- statement:
--   The Flow Isotropic Pairs construction uses the e facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowIsotropicPairs.lean#L101-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowIsotropicPairs.lean#L101-L130

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

theorem ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs.e_facts (X : Data E r) {ξ x : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0) (hξ0 : ξ ≠ 0)
    (hxξ : herm X.Gm x ξ = 0) (hxx : herm X.Gm x x = 0) {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.dom)
    (e : X.Ψ → Fin r → ℂ) (hxp0 : ∀ τ, X.ucomp z0 ξ (X.embV x) τ ≠ 0)
    (he : ∀ τ, e τ = ((Real.sqrt (X.c τ * X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)))⁻¹ : ℂ) •
      X.ucomp z0 ξ (X.embV x) τ) :
    X.IsIsoV e ∧ (∀ τ, hermC τ.1 X.Gm (e τ) (Data.emb τ.1 ξ) = 0) ∧
      (∀ τ, X.Hf z0 τ (e τ) (Data.emb τ.1 ξ) = 0) ∧ (∀ τ, X.c τ * X.maj z0 τ (e τ) = 1) := by sorry
