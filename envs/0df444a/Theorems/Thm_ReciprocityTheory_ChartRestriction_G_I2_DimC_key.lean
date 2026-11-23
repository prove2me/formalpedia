-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_key
-- name    : ReciprocityTheory.ChartRestriction.G.I2.DimC.key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:11.855154+00:00
-- url     : https://prove2.me/theorems/80bb1d1c-0a21-4009-a9bd-a33bec2bcc3a
-- title:
--   Dim C: key
-- statement:
--   The Dim C construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ExistsPairs.lean#L241-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ExistsPairs.lean#L241-L271

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
variable {Y} (e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι)
  (hee : ∀ i j, (Hf (e i) (e j)).im = 0)
  (hef : ∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0)
include hee hef

theorem ReciprocityTheory.ChartRestriction.G.I2.DimC.key (z : Fin (Fintype.card ι) → ℂ) (j : Fin (Fintype.card ι)) :
    Hf (Phi e z) (f j) = (∑ i, ∑ l, z i * tau e f hee hef j l * S e i l) + 2 * I * z j := by sorry
