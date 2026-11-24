-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hon_shape
-- name    : ReciprocityTheory.ChartRestriction.L1.hon_shape
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:24:58.887582+00:00
-- url     : https://prove2.me/theorems/9ceb1c71-1800-4f8d-a600-9339a9c93f7d
-- title:
--   L1: hon shape
-- statement:
--   The L1 construction uses the hon shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/SubstOfLog.lean#L88-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/SubstOfLog.lean#L88-L119

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_DivByPartialYAtZeroSubstAtXAtY
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SubstOfLog
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

theorem ReciprocityTheory.ChartRestriction.L1.hon_shape (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam) :
    ∃ hh : PowerSeries K,
      HomCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) Φ A hh ∧
      DivBy (l : K) (e - hh.subst ((X : PowerSeries K) ^ (l ^ 2))) ∧
      coeff 1 hh = coeff (l ^ 2) e := by sorry
