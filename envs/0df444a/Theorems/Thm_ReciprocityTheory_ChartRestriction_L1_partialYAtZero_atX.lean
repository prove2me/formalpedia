-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_partialYAtZero_atX
-- name    : ReciprocityTheory.ChartRestriction.L1.partialYAtZero_atX
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:54:50.906447+00:00
-- url     : https://prove2.me/theorems/b377ac23-0f13-4975-af9b-50f260f277d1
-- title:
--   L1: partial YAt Zero at X
-- statement:
--   The L1 construction uses the partial YAt Zero at X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L136-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L136-L142

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

theorem ReciprocityTheory.ChartRestriction.L1.partialYAtZero_atX (D : PowerSeries K) : d2 (atX D) = 0 := by sorry
