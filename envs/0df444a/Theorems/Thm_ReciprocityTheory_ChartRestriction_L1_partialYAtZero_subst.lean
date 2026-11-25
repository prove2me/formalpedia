-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_partialYAtZero_subst
-- name    : ReciprocityTheory.ChartRestriction.L1.partialYAtZero_subst
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:19.386229+00:00
-- url     : https://prove2.me/theorems/f8066257-b202-5bd9-904f-a63d166cd16c
-- title:
--   L1: partial YAt Zero subst
-- statement:
--   The L1 construction uses the partial YAt Zero subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L131-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonB.lean#L131-L134

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

theorem ReciprocityTheory.ChartRestriction.L1.partialYAtZero_subst (D : PowerSeries K) {P : MvPowerSeries (Fin 2) K}
    (hP : MvPowerSeries.constantCoeff P = 0) :
    d2 (D.subst P) = (derivative K D).subst (ev0 P) * d2 P := by sorry
