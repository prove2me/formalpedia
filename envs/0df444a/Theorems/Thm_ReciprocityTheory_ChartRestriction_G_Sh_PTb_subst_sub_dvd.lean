-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_subst_sub_dvd
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.subst_sub_dvd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:35:25.51291+00:00
-- url     : https://prove2.me/theorems/6576fbe9-576b-4ddd-bdab-06dfccdc4d71
-- title:
--   PTb: subst sub dvd
-- statement:
--   The PTb construction uses the subst sub dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CardToMultisetEqDegree.lean#L64-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CardToMultisetEqDegree.lean#L64-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
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
variable {C : Type} [Field C]

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.subst_sub_dvd {d : ℕ} (f : MvPowerSeries (Fin d) C)
    (hf : ∀ e : Fin d →₀ ℕ, e.degree ≤ 1 → coeff e f = 0)
    (α β : Fin d → PowerSeries C) (hα : ∀ b, PowerSeries.constantCoeff (α b) = 0)
    (hβ : ∀ b, PowerSeries.constantCoeff (β b) = 0) (k : ℕ)
    (hk : ∀ b, (PowerSeries.X : PowerSeries C) ^ k ∣ α b - β b) :
    (PowerSeries.X : PowerSeries C) ^ (k + 1) ∣ subst α f - subst β f := by sorry
