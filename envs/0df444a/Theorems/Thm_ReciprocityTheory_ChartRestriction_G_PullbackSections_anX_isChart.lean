-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anX_isChart
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.anX_isChart
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T18:15:56.361435+00:00
-- url     : https://prove2.me/theorems/6a7ce213-a605-4cca-82ca-e63d94739a19
-- title:
--   Pullback Sections: an X is Chart
-- statement:
--   The Pullback Sections construction uses the an X is Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnChartAsm.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnChartAsm.lean#L20-L32

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnLawX
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_ComposeLinearAction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartAsm
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
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} [Algebra c.F ℂ]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.anX_isChart [StarRing (𝓞 E)] (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (y : FrPt Xo c ℂ) (hy : y.x = F.u i P) (e' : Fin g ≃ Lt1 Dw)
    (hder : ∀ ℓ : Lt1 Dw, IsDerivAt0 (anE F i P) (Pi.single (e'.symm ℓ) 1) (y.u ℓ.1 ℓ.2))
    (hPair : IsHolTo (Set.univ : Set (Fin (2 * g) → ℂ)) fun v =>
      pullback.lift (F.ex i P (anPr 0 v)).left (F.ex i P (anPr 1 v)).left
        ((Over.w (F.ex i P (anPr 0 v))).trans (Over.w (F.ex i P (anPr 1 v))).symm)) :
    IsChart y g (anFB ty).G.F (anFB ty).A.act (anUvec e') (anX F i P hP y hy) := by sorry
