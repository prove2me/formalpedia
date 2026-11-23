-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_FlatBC_gs_isoRel
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.gs_isoRel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:31.034806+00:00
-- url     : https://prove2.me/theorems/f0799137-9f3c-4b23-ab76-af9f9c1ffd99
-- title:
--   Flat BC: gs iso Rel
-- statement:
--   The Flat BC construction uses the gs iso Rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L485-L493
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L485-L493

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.gs_isoRel {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M} (h : IsoRel w s s') (i : M.ι) (k : L.ι) (y : Y)
    (hi : y ∈ M.U i) (hk : y ∈ L.U k) :
    gs (𝟙 Y) y (M.U i) (s'.f i) = (gm (𝟙 Y) y ((LB.div M L).U (i, k)) (w.s (i, k))).val * gs (𝟙 Y) y (L.U k) (s.f k) := by sorry
