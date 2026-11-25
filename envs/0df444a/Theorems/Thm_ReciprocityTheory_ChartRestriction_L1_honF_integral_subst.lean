-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_honF_integral_subst
-- name    : ReciprocityTheory.ChartRestriction.L1.honF_integral_subst
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:45:43.392533+00:00
-- url     : https://prove2.me/theorems/5d181e3e-9821-4fd2-b483-785cd653d2d5
-- title:
--   L1: hon F integral subst
-- statement:
--   The L1 construction uses the hon F integral subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonF.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonF.lean#L74-L76

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SubstOfLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonF
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
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem ReciprocityTheory.ChartRestriction.L1.honF_integral_subst {f g : PowerSeries K} (hf : IntegralPS f) (hg0 : constantCoeff g = 0)
    (hg : IntegralPS g) : IntegralPS (f.subst g) := by sorry
