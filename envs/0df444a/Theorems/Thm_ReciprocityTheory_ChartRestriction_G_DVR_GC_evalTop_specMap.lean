-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_GC_evalTop_specMap
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_specMap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:12:10.282988+00:00
-- url     : https://prove2.me/theorems/aa1f263a-ddf7-442b-b828-97f02771e288
-- title:
--   GC: eval Top spec Map
-- statement:
--   The GC construction uses the eval Top spec Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenCalc.lean#L116-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenCalc.lean#L116-L125

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_specMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (U : (Spec (CommRingCat.of A)).Opens) (hU : U = ⊤)
    (hU' : Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ U = ⊤) (a : Γ(Spec (CommRingCat.of A), U)) :
    evalTop _ hU' (((Spec.map (CommRingCat.ofHom f)).app U).hom a) = f (evalTop U hU a) := by sorry
