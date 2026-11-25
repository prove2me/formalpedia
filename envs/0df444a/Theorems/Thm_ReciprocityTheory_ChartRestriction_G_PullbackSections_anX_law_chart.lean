-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anX_law_chart
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.anX_law_chart
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T18:21:04.713181+00:00
-- url     : https://prove2.me/theorems/411445f8-33b7-5b78-8501-d643d4d769a8
-- title:
--   Pullback Sections: an X law chart
-- statement:
--   The Pullback Sections construction uses the an X law chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnLawX.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnLawX.lean#L22-L29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnLawX
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
open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} [Algebra c.F ℂ]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.anX_law_chart (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (y : FrPt Xo c ℂ) (hy : y.x = F.u i P)
    (hPair : IsHolTo (Set.univ : Set (Fin (2 * g) → ℂ)) fun v =>
      pullback.lift (F.ex i P (anPr 0 v)).left (F.ex i P (anPr 1 v)).left
        ((Over.w (F.ex i P (anPr 0 v))).trans (Over.w (F.ex i P (anPr 1 v))).symm)) (m : ℕ) :
    homAt y.x (jetSubstP m fun p : Fin 1 × Fin g => psTrunc m (addF ℂ g p.2)) ≫ anX F i P hP y hy m =
      jpt y g (anX F i P hP y hy) m (0 : Fin 2) * jpt y g (anX F i P hP y hy) m (1 : Fin 2) := by sorry
