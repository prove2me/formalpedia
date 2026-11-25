-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hon_main
-- name    : ReciprocityTheory.ChartRestriction.L1.hon_main
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:45:55.039692+00:00
-- url     : https://prove2.me/theorems/e63c7c8f-67a8-588d-a13a-0ed002830b3a
-- title:
--   L1: hon main
-- statement:
--   The L1 construction uses the hon main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonH.lean#L220-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonH.lean#L220-L256

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonH
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
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] {l : ℕ}
  {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem ReciprocityTheory.ChartRestriction.L1.hon_main (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i e‖ = 1) :
    ∃ c : K, ‖c‖ = 1 ∧ IntegralPS (lam - (c / (l : K)) •
      (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2))) := by sorry
