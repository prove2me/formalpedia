-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowIsotropicPairs_flow_facts
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs.flow_facts
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:23:57.713391+00:00
-- url     : https://prove2.me/theorems/d670d8ec-d2b6-57d9-9362-7d725510d844
-- title:
--   Flow Isotropic Pairs: flow facts
-- statement:
--   The Flow Isotropic Pairs construction uses the flow facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowIsotropicPairs.lean#L132-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowIsotropicPairs.lean#L132-L150

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

theorem ReciprocityTheory.ChartRestriction.G.FD.FlowIsotropicPairs.flow_facts (X : Data E r) {ξ : Fin r → E} {z0 : Frame X.Ψ r} (hz0 : z0 ∈ X.FramesOverBasis ξ)
    (e : X.Ψ → Fin r → ℂ) (hiso : X.IsIsoV e)
    (heξ : ∀ τ, hermC τ.1 X.Gm (e τ) (Data.emb τ.1 ξ) = 0)
    (hHe : ∀ τ, X.Hf z0 τ (e τ) (Data.emb τ.1 ξ) = 0) (hce : ∀ τ, X.c τ * X.maj z0 τ (e τ) = 1)
    {z : Frame X.Ψ r} (hz : z ∈ X.dom) (hf : X.SameFlag z0 z) :
    (∀ τ, X.ttV e z τ = 1) ∧ X.flowV e (fun _ => -(I / 2)) z ∈ X.FramesOverBasis ξ := by sorry
