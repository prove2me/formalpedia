-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_germ_nbhdLift
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.germ_nbhdLift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:54:37.162609+00:00
-- url     : https://prove2.me/theorems/064abe3b-0420-4b55-b59a-55d89ac0a3f8
-- title:
--   Pullback Sections: germ nbhd Lift
-- statement:
--   The Pullback Sections construction uses the germ nbhd Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetA.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetA.lean#L54-L58

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.germ_nbhdLift (ψ : ∀ U : Y.Opens, y₀ ∈ U → (Γ(Y, U) ⟶ A))
    (hψ : ∀ (U V : Y.Opens) (hU : y₀ ∈ U) (hV : y₀ ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ ψ V hV = ψ U hU) (U : Y.Opens) (hU : y₀ ∈ U) :
    Y.presheaf.germ U y₀ hU ≫ nbhdLift y₀ A ψ hψ = ψ U hU := by sorry
