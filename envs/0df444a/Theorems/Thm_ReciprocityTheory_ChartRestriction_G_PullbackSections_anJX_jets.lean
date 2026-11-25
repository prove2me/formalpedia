-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anJX_jets
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.anJX_jets
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T17:43:15.009693+00:00
-- url     : https://prove2.me/theorems/5e7d2222-4569-5df7-8e8d-47d3e003b939
-- title:
--   Pullback Sections: an JX jets
-- statement:
--   The Pullback Sections construction uses the an JX jets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnHolFamOfHolTo.lean#L199-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnHolFamOfHolTo.lean#L199-L206

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
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
open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {Y : Scheme.{0}}
variable {X : Scheme.{0}} {G : Over X} [MonObj G] {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.anJX_jets {u : Sp ℂ ⟶ X} (ex : (Fin g → ℂ) → (Over.mk u ⟶ G)) (hol : IsHolFam fun z => (ex z).left) (m : ℕ)
    (A : (Fin (2 * g) → ℂ) →L[ℂ] (Fin g → ℂ)) (hA : IsHolFam fun v => (ex (A v)).left) :
    spMap ((jetMap (anLin A) (anLin_mem A) : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin (2 * g)) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin (2 * g)) m) ≫ jetPt (fun z => (ex z).left) hol m =
      jetPt (fun v => (ex (A v)).left) hA m := by sorry
