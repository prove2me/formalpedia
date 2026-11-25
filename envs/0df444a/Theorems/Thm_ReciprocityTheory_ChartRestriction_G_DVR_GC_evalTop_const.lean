-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_GC_evalTop_const
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_const
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:14:43.886474+00:00
-- url     : https://prove2.me/theorems/4523cd7c-5eb3-5ad3-918c-3d632eab1c1d
-- title:
--   GC: eval Top const
-- statement:
--   The GC construction uses the eval Top const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenCalc.lean#L161-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenCalc.lean#L161-L166

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_const {A : Type} [CommRing A] (U : (Spec (CommRingCat.of A)).Opens) (hU : U = ⊤) (x : A) :
    evalTop U hU (((Spec (CommRingCat.of A)).presheaf.map (homOfLE le_top).op).hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x)) = x := by sorry
