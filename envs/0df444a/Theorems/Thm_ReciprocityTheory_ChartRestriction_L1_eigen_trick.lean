-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_eigen_trick
-- name    : ReciprocityTheory.ChartRestriction.L1.eigen_trick
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:44:54.706719+00:00
-- url     : https://prove2.me/theorems/fe63fa78-40fe-4db4-873e-507a7f86b817
-- title:
--   L1: eigen trick
-- statement:
--   The L1 construction uses the eigen trick property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonD.lean#L115-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonD.lean#L115-L123

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD
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

theorem ReciprocityTheory.ChartRestriction.L1.eigen_trick {A : PowerSeries K} {b : K} (hA0 : constantCoeff A = 0) (D : PowerSeries K)
    (hD0 : constantCoeff D = 0) (h : DivBy (l : K) (D.subst A - C b * D))
    (hb : ‖coeff 1 A - b‖ = 1) : ‖coeff 1 D‖ ≤ ‖(l : K)‖ := by sorry
