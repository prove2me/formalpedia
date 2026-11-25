-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_twC_of_not_dvd
-- name    : ReciprocityTheory.ChartRestriction.L1.twC_of_not_dvd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:48:40.228638+00:00
-- url     : https://prove2.me/theorems/5ba384d7-9f60-55b4-95ca-3c3dc804225f
-- title:
--   L1: tw C of not dvd
-- statement:
--   The L1 construction uses the tw C of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonH.lean#L159-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonH.lean#L159-L164

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

theorem ReciprocityTheory.ChartRestriction.L1.twC_of_not_dvd (τ : K →+* K) {n i : ℕ} (hd : ¬ (l ^ 2) ^ i ∣ n) (j : ℕ) :
    twC l τ lam n (i + j) = 0 := by sorry
