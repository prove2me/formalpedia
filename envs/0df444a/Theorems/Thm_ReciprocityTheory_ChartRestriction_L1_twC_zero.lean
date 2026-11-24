-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_twC_zero
-- name    : ReciprocityTheory.ChartRestriction.L1.twC_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:38:28.345815+00:00
-- url     : https://prove2.me/theorems/d23750bb-f5a3-4658-9acb-dfaa30fb33f2
-- title:
--   L1: tw C zero
-- statement:
--   The L1 construction uses the tw C zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonH.lean#L137-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonH.lean#L137-L138

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

theorem ReciprocityTheory.ChartRestriction.L1.twC_zero (τ : K →+* K) (n : ℕ) : twC l τ lam n 0 = coeff n lam := by sorry
