-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anX_trunc
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.anX_trunc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:53:03.580735+00:00
-- url     : https://prove2.me/theorems/de6eb651-e77b-4c60-ad8d-16355b50c809
-- title:
--   Pullback Sections: an X trunc
-- statement:
--   The Pullback Sections construction uses the an X trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnChartX.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnChartX.lean#L60-L65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
variable [Algebra c.F ℂ]
variable (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P)
  (y : FrPt Xo c ℂ) (hy : y.x = F.u i P)

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.anX_trunc (m : ℕ) :
    homAt y.x (jetTrunc : Jet ℂ (Fin 1 × Fin g) (m + 1) →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) ≫ anX F i P hP y hy (m + 1) =
      anX F i P hP y hy m := by sorry
