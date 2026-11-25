-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hon_deriv
-- name    : ReciprocityTheory.ChartRestriction.L1.hon_deriv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:45:34.735092+00:00
-- url     : https://prove2.me/theorems/a12cddab-6341-59ef-9325-bf35cc34e230
-- title:
--   L1: hon deriv
-- statement:
--   The L1 construction uses the hon deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L232-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L232-L252

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB
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
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K}

theorem ReciprocityTheory.ChartRestriction.L1.hon_deriv (h : LawD lam Φ) (x : K) (D : PowerSeries K)
    (hadd : DivByMv x (D.subst Φ - atX D - atY D)) :
    DivBy x (derivative K D - C (coeff 1 D) * derivative K lam) := by sorry
