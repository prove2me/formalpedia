-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jets_law
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.jets_law
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T17:50:39.836862+00:00
-- url     : https://prove2.me/theorems/9f5407ca-d318-5c0e-b377-533524ca8b12
-- title:
--   Pullback Sections: jets law
-- statement:
--   The Pullback Sections construction uses the jets law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnHolFamOfHolTo.lean#L208-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnHolFamOfHolTo.lean#L208-L274

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Theorems.Thm_Formalism_L2_Pj_ex_add

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.jets_law (u : Sp ℂ ⟶ X) {u' : Sp ℂ ⟶ X} (ex : (Fin g → ℂ) → (Over.mk u' ⟶ G))
    (hol : IsHolFam fun z => (ex z).left) (xm : ∀ m, overAt u (Jet ℂ (Fin 1 × Fin g) m) ⟶ G)
    (hx : ∀ m, (xm m).left = jetPt (fun z => (ex z).left) hol m)
    (ex_add : ∀ z w, ex (z + w) = ex z * ex w)
    (hP : IsHolTo (Set.univ : Set (Fin (2 * g) → ℂ)) fun v =>
      pullback.lift (ex (anPr 0 v)).left (ex (anPr 1 v)).left
        ((Over.w (ex (anPr 0 v))).trans (Over.w (ex (anPr 1 v))).symm))
    (m : ℕ) :
    homAt u (jetSubstP (S := ℂ) m fun p : Fin 1 × Fin g => psTrunc m (addF ℂ g p.2)) ≫ xm m =
      (homAt u (jetCopy (S := ℂ) g m (0 : Fin 2)) ≫ xm m) * (homAt u (jetCopy (S := ℂ) g m (1 : Fin 2)) ≫ xm m) := by sorry
