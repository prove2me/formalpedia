-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hon_level
-- name    : ReciprocityTheory.ChartRestriction.L1.hon_level
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:46:00.151049+00:00
-- url     : https://prove2.me/theorems/f8372705-b0a2-558b-99c9-4770f2aadd3f
-- title:
--   L1: hon level
-- statement:
--   The L1 construction uses the hon level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/SubstOfLog.lean#L121-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/SubstOfLog.lean#L121-L135

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

theorem ReciprocityTheory.ChartRestriction.L1.hon_level (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i e‖ = 1) : ‖coeff (l ^ 2) e‖ = 1 := by sorry
