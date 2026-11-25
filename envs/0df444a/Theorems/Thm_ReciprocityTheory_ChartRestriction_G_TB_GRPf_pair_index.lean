-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_pair_index
-- name    : ReciprocityTheory.ChartRestriction.G.TB.GRPf.pair_index
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:09.080001+00:00
-- url     : https://prove2.me/theorems/be65798f-7690-518f-a924-c165c7d6f412
-- title:
--   GRPf: pair index
-- statement:
--   The GRPf construction uses the pair index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeRatio.lean#L71-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeRatio.lean#L71-L96

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeRatio
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
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GRPf
variable {O k : Type} [CommRing O] [StarRing O] [CommRing k] [Algebra ℚ k]
variable {T : Type} (χ : T → O →+* k) (cc : T → T) (hcc : ∀ σ a, χ (cc σ) a = χ σ (star a))
  (hunit : ∀ σ τ, σ ≠ τ → ∃ a, IsUnit (χ σ a - χ τ a))
include hunit
include hcc

theorem ReciprocityTheory.ChartRestriction.G.TB.GRPf.pair_index {c : k} (hc : c ≠ 0) (σ σ' : T)
    (h : ∀ a, c * (χ σ a * χ σ (star a) + χ σ' a * χ σ' (star a) - 2 * χ σ a * χ σ' a) = 0) : σ' = cc σ := by sorry
