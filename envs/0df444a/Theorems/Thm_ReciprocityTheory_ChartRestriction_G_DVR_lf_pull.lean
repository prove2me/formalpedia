-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_pull
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.lf_pull
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:11:25.623224+00:00
-- url     : https://prove2.me/theorems/a99b11e6-19f6-575f-88cb-62b35164b52b
-- title:
--   DVR: lf pull
-- statement:
--   The DVR construction uses the lf pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L36-L40

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T T' : Over S}

theorem ReciprocityTheory.ChartRestriction.G.DVR.lf_pull (h : T' ⟶ T) (F : (T ⟶ A) →₀ ℤ) :
    Finsupp.mapDomain (fun ψ => h.left ≫ ψ) (lf F) = lf (Finsupp.mapDomain (fun x => h ≫ x) F) := by sorry
