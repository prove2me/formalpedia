-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_GC_evalTop_comp
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_comp
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:14:39.214844+00:00
-- url     : https://prove2.me/theorems/dd87d78d-1102-54c1-870b-8ccf5936b322
-- title:
--   GC: eval Top comp
-- statement:
--   The GC construction uses the eval Top comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenCalc.lean#L139-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenCalc.lean#L139-L147

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.GC
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F]
set_option maxHeartbeats 800000

theorem ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_comp {Y : Scheme.{0}} (g : Spec (CommRingCat.of F) ⟶ Y) (e : Spec (CommRingCat.of V) ⟶ Y)
    (hg : g = DegPre.jFR (R := V) F ≫ e) (U : Y.Opens) (hU : e ⁻¹ᵁ U = ⊤) (hU' : g ⁻¹ᵁ U = ⊤)
    (a : Γ(Y, U)) :
    evalTop _ hU' ((g.app U).hom a) =
      algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (evalTop _ hU ((e.app U).hom a))) := by sorry
