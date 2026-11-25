-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_FlatBC_gs_dfun
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.gs_dfun
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:10:33.734821+00:00
-- url     : https://prove2.me/theorems/f000b6bc-2d42-5d48-9861-3a8326a47af8
-- title:
--   Flat BC: gs dfun
-- statement:
--   The Flat BC construction uses the gs dfun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L120-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/FlatBCSec.lean#L120-L126

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
open AlgebraicGeometry CategoryTheory TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR
variable {Y : Scheme.{0}} (L : LB Y) {n : ℕ} (V : Fin n → Y.Opens) (c : Fin n → L.ι) (hVc : ∀ k, V k ≤ L.U (c k))
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.gs_dfun {f : ∀ k, Γ(Y, V k)} (hf : dfun L V c hVc f = 0) (k l : Fin n) (y : Y) (hk : y ∈ V k) (hl : y ∈ V l) :
    gs (𝟙 Y) y (V k) (f k) = (gm (𝟙 Y) y (L.U (c k) ⊓ L.U (c l)) (L.g (c k) (c l))).val * gs (𝟙 Y) y (V l) (f l) := by sorry
