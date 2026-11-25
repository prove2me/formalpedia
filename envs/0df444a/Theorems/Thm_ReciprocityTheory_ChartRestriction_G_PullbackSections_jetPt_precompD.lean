-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_precompD
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.jetPt_precompD
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:44:06.444189+00:00
-- url     : https://prove2.me/theorems/2586a0e9-ab54-55e3-a9c8-bfe0697f15b7
-- title:
--   Pullback Sections: jet Pt precomp D
-- statement:
--   The Pullback Sections construction uses the jet Pt precomp D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnHolFamOfHolTo.lean#L84-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnHolFamOfHolTo.lean#L84-L113

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
set_option backward.isDefEq.respectTransparency false

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.jetPt_precompD {g g' : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (e' : (Fin g' → ℂ) → (Sp ℂ ⟶ Y))
    (hol : IsHolFam e) (hol' : IsHolFam e') (h0 : e' 0 = e 0) (m : ℕ)
    (χ : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g') m) [hχl : IsLocalHom χ]
    (hχ : ∀ (U : Y.Opens) (_ : e 0 cpt ∈ U) (f : Γ(Y, U)),
      χ (jetOf m (fun z => valAt' (e z) U f)) = jetOf m (fun z => valAt' (e' z) U f)) :
    spMap χ ≫ jetPt e hol m = jetPt e' hol' m := by sorry
