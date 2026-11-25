-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_geom_sum_root
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.geom_sum_root
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:35:25.338826+00:00
-- url     : https://prove2.me/theorems/c259b43c-987e-4e6e-a015-2738d229106c
-- title:
--   PTb: geom sum root
-- statement:
--   The PTb construction uses the geom sum root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/GeomSumRoot.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/GeomSumRoot.lean#L12-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_GeomSumRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.geom_sum_root {p : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ p) (m : ℕ) :
    ∑ j ∈ Finset.range p, (ζ ^ m) ^ j = if p ∣ m then (p : C) else 0 := by sorry
