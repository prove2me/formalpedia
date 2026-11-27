-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TWM_exists_ratio
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TWM.exists_ratio
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-27T06:28:22.381061+00:00
-- url     : https://prove2.me/theorems/9a25530f-466d-5bb4-b004-0b3678be79b7
-- title:
--   TWM: exists ratio
-- statement:
--   The TWM construction uses the exists ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/VRatioGtStatement.lean#L36-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/VRatioGtStatement.lean#L36-L67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LiftOUnique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PeriodicValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ConstBFMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsRosatiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_VRatioGtStatement
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TWM
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation QForm
variable {V : Type} [CommRing V] [IsDomain V] {F : Type} [Field F] [Algebra (FractionRing V) F] {X : Scheme.{0}}
  {L : LB X}

theorem ReciprocityTheory.ChartRestriction.G.DVR.TWM.exists_ratio (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Spec (CommRingCat.of F) ⟶ X)}
    {ε : K → ℤ} {φ' : K' → (Spec (CommRingCat.of F) ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (t' : LB.Gen (LB.LinComb L φ' ε')) (ht' : t'.IsGen) (hf : FormEq φ ε φ' ε') :
    ∃ c : F, c ≠ 0 ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (J), Good L z J →
      (val t r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * (val t' r z J).val := by sorry
