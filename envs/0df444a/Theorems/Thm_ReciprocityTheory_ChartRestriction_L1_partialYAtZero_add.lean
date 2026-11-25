-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_partialYAtZero_add
-- name    : ReciprocityTheory.ChartRestriction.L1.partialYAtZero_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:48:03.229337+00:00
-- url     : https://prove2.me/theorems/d7dc46f0-fd57-5d03-9478-ab837d44f1c3
-- title:
--   L1: partial YAt Zero add
-- statement:
--   The L1 construction uses the partial YAt Zero add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L160-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L160-L162

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

theorem ReciprocityTheory.ChartRestriction.L1.partialYAtZero_add (F G : MvPowerSeries (Fin 2) K) : d2 (F + G) = d2 F + d2 G := by sorry
