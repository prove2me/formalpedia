-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_GC_evalTop_res
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:29.749002+00:00
-- url     : https://prove2.me/theorems/742c2b4e-15af-45b8-b52b-d5c0c5143dd7
-- title:
--   GC: eval Top res
-- statement:
--   The GC construction uses the eval Top res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenCalc.lean#L110-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenCalc.lean#L110-L114

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_res {A : Type} [CommRing A] {U U' : (Spec (CommRingCat.of A)).Opens} (h : U' ≤ U)
    (hU : U = ⊤) (hU' : U' = ⊤) (a : Γ(Spec (CommRingCat.of A), U)) :
    evalTop U' hU' (((Spec (CommRingCat.of A)).presheaf.map (homOfLE h).op).hom a) = evalTop U hU a := by sorry
