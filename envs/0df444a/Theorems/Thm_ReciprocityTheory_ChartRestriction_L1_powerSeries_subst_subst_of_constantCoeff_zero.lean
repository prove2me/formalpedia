-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_powerSeries_subst_subst_of_constantCoeff_zero
-- name    : ReciprocityTheory.ChartRestriction.L1.powerSeries_subst_subst_of_constantCoeff_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:46:11.794405+00:00
-- url     : https://prove2.me/theorems/2f92bfdd-106c-45f2-9e47-cefbe6803f39
-- title:
--   L1: power Series subst subst of constant Coeff zero
-- statement:
--   The L1 construction uses the power Series subst subst of constant Coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgMulN.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgMulN.lean#L12-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgMulN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

theorem ReciprocityTheory.ChartRestriction.L1.powerSeries_subst_subst_of_constantCoeff_zero {R : Type} [CommRing R] {α β : Type} (φ : PowerSeries R)
    {u : MvPowerSeries α R} (hu : MvPowerSeries.constantCoeff u = 0) {b : α → MvPowerSeries β R}
    (hb : MvPowerSeries.HasSubst b) : (φ.subst u).subst b = φ.subst (u.subst b) := by sorry
