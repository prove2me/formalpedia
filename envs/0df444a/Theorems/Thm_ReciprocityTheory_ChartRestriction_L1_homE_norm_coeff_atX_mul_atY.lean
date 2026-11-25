-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_homE_norm_coeff_atX_mul_atY
-- name    : ReciprocityTheory.ChartRestriction.L1.homE_norm_coeff_atX_mul_atY
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:45:35.025707+00:00
-- url     : https://prove2.me/theorems/49b1a08a-0bf6-56ac-8507-325753237011
-- title:
--   L1: hom E norm coeff at X mul at Y
-- statement:
--   The L1 construction uses the hom E norm coeff at X mul at Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/DivByPartialYAtZeroSubstAtXAtY.lean#L51-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/DivByPartialYAtZeroSubstAtXAtY.lean#L51-L71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_DivByPartialYAtZeroSubstAtXAtY
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
variable {lam₁ lam₂ : PowerSeries K} {Φ₁ Φ₂ : MvPowerSeries (Fin 2) K} {A₁ A₂ g : PowerSeries K}

theorem ReciprocityTheory.ChartRestriction.L1.homE_norm_coeff_atX_mul_atY {x : K} (a b : PowerSeries K) (ha : IntegralPS a)
    (hb : ‖coeff 1 b‖ ≤ ‖x‖) (n : ℕ) :
    ‖MvPowerSeries.coeff (Finsupp.single 0 n + Finsupp.single 1 1) (atX a * atY b)‖ ≤ ‖x‖ := by sorry
