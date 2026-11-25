-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_hF_per
-- name    : ReciprocityTheory.ChartRestriction.G.I2.DimC.hF_per
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:27:39.916462+00:00
-- url     : https://prove2.me/theorems/cbc4fb4c-1930-44c0-af23-91a11c32ca9a
-- title:
--   Dim C: h F per
-- statement:
--   The Dim C construction uses the h F per property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ExistsPairs.lean#L287-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ExistsPairs.lean#L287-L319

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex Module
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.DimC
variable {ι : Type} [Fintype ι]
variable (Y : GT ι)
variable (e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι)
  (hee : ∀ i j, (Hf (e i) (e j)).im = 0)
  (hef : ∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0)
include hee

theorem ReciprocityTheory.ChartRestriction.G.I2.DimC.hF_per (he : ∀ i, e i ∈ lat Y.b) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) (hFs : F ∈ Y.Sec q)
    (l : Fin (Fintype.card ι)) (z : Fin (Fintype.card ι) → ℂ) :
    hF Y e q F (z + Pi.single l 1) = hF Y e q F z := by sorry
