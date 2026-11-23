-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_sval_lin
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.sval_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:37.102338+00:00
-- url     : https://prove2.me/theorems/a5c96025-9c59-4ccc-b57a-89180c6dc6f9
-- title:
--   Section Scalar Valuation: sval lin
-- statement:
--   The Section Scalar Valuation construction uses the sval lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/SectionScalarValuation.lean#L80-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/SectionScalarValuation.lean#L80-L92

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

theorem ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.sval_lin {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)}
    {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε))
    (hs : ∀ j : K → L.ι, s.f j = ∑ i, resTop (LB.wchart L φ j) (b i) * (show Γ(Y, LB.wchart L φ j) from (t i).f j)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s r z J = ∑ i, gs r z ⊤ (b i) * sval (t i) r z J := by sorry
