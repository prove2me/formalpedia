-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_exists_pairs
-- name    : ReciprocityTheory.ChartRestriction.G.I2.DimC.exists_pairs
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:27:47.201194+00:00
-- url     : https://prove2.me/theorems/a5a278b4-9a02-4a10-b64b-977bb09bb838
-- title:
--   Dim C: exists pairs
-- statement:
--   The Dim C construction uses the exists pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ExistsPairs.lean#L118-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ExistsPairs.lean#L118-L126

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

theorem ReciprocityTheory.ChartRestriction.G.I2.DimC.exists_pairs : ∃ e f : Fin (Fintype.card ι) → EuclideanSpace ℂ ι,
    (∀ i, e i ∈ lat Y.b) ∧ (∀ j, f j ∈ lat Y.b) ∧ (∀ i j, (Hf (e i) (e j)).im = 0) ∧
    (∀ i j, (Hf (e i) (f j)).im = if i = j then 1 else 0) := by sorry
