-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_T_apply
-- name    : ReciprocityTheory.ChartRestriction.G.I2.DimC.T_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:27:32.28556+00:00
-- url     : https://prove2.me/theorems/f743b909-b782-4dfe-bea9-eb8eb129b3a0
-- title:
--   Dim C: T apply
-- statement:
--   The Dim C construction uses the T apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ExistsPairs.lean#L424-L425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ExistsPairs.lean#L424-L425

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

theorem ReciprocityTheory.ChartRestriction.G.I2.DimC.T_apply (q : ℕ) (F : Y.Sec q) (r : Fin (Fintype.card ι) → Fin q) :
    T Y e q F r = DimB.Av (DimB.Pm (hF Y e q F.1) (fun l => ((r l : ℕ) : ℤ))) 0 := by sorry
