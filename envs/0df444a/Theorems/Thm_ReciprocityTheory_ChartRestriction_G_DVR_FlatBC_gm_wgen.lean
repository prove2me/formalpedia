-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_FlatBC_gm_wgen
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.gm_wgen
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:10:33.354254+00:00
-- url     : https://prove2.me/theorems/df393456-eb06-52d7-9d04-bb3862475e0e
-- title:
--   Flat BC: gm wgen
-- statement:
--   The Flat BC construction uses the gm wgen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L516-L527
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L516-L527

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FlatBCSec
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
open TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.FlatBC
variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
open AlgebraicGeometry CategoryTheory TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {Y : Scheme.{0}} {L M : LB Y}

theorem ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.gm_wgen {w : LB.Iso L M} (hw : w.IsGen) (i i' : M.ι) (k k' : L.ι) (y : Y) (hi : y ∈ M.U i) (hi' : y ∈ M.U i')
    (hk : y ∈ L.U k) (hk' : y ∈ L.U k') :
    gm (𝟙 Y) y ((LB.div M L).U (i, k)) (w.s (i, k)) =
      gm (𝟙 Y) y (M.U i ⊓ M.U i') (M.g i i') * (gm (𝟙 Y) y (L.U k ⊓ L.U k') (L.g k k'))⁻¹ *
        gm (𝟙 Y) y ((LB.div M L).U (i', k')) (w.s (i', k')) := by sorry
