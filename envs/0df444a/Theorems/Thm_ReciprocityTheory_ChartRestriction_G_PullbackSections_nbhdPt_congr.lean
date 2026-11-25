-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_nbhdPt_congr
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.nbhdPt_congr
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:33:14.356676+00:00
-- url     : https://prove2.me/theorems/cceeae30-eb12-4300-a0b5-ec38ac12c1f7
-- title:
--   Pullback Sections: nbhd Pt congr
-- statement:
--   The Pullback Sections construction uses the nbhd Pt congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetA.lean#L132-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetA.lean#L132-L139

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
variable {Y : Scheme.{0}}
variable (y₀ : Y) (A : CommRingCat.{0})
variable {y₀ A}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.nbhdPt_congr {ψ ψ' : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A)}
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU)
    (hψ' : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ' V hV = ψ' U hU)
    (e : ∀ U hU, ψ U hU = ψ' U hU) : nbhdPt ψ hψ = nbhdPt ψ' hψ' := by sorry
