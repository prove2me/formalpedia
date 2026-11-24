-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_partialYAtZero_sub
-- name    : ReciprocityTheory.ChartRestriction.L1.partialYAtZero_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:55:10.619986+00:00
-- url     : https://prove2.me/theorems/16dc78e4-06ae-4ce5-bbf8-e7e3987029f4
-- title:
--   L1: partial YAt Zero sub
-- statement:
--   The L1 construction uses the partial YAt Zero sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L156-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L156-L158

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

theorem ReciprocityTheory.ChartRestriction.L1.partialYAtZero_sub (F G : MvPowerSeries (Fin 2) K) : d2 (F - G) = d2 F - d2 G := by sorry
