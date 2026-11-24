-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_divBy_partialYAtZero
-- name    : ReciprocityTheory.ChartRestriction.L1.divBy_partialYAtZero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:54:52.049357+00:00
-- url     : https://prove2.me/theorems/84175d5e-caa5-4551-8bcd-2ce756775b13
-- title:
--   L1: div By partial YAt Zero
-- statement:
--   The L1 construction uses the div By partial YAt Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L124-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L124-L129

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

theorem ReciprocityTheory.ChartRestriction.L1.divBy_partialYAtZero {x : K} {F : MvPowerSeries (Fin 2) K} (hF : DivByMv x F) : DivBy x (d2 F) := by sorry
