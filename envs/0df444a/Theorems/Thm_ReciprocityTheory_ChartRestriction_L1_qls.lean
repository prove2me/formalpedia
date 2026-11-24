-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_qls
-- name    : ReciprocityTheory.ChartRestriction.L1.qls
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:53:48.851874+00:00
-- url     : https://prove2.me/theorems/b5126530-ce00-4c04-9c22-7645d8fc4e02
-- title:
--   L1: qls
-- statement:
--   The L1 construction uses the qls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonA.lean#L137-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonA.lean#L137-L191

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonA
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

theorem ReciprocityTheory.ChartRestriction.L1.qls {ι : Type} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (z : PowerSeries K)
    (hz0 : constantCoeff z = 0) (hz : IntegralPS (derivative K z)) (P Q : MvPowerSeries ι K)
    (hP0 : MvPowerSeries.constantCoeff P = 0) (hQ0 : MvPowerSeries.constantCoeff Q = 0)
    (hP : IntegralMv P) (hQ : IntegralMv Q) (hPQ : DivByMv (l : K) (P - Q)) :
    DivByMv (l : K) (z.subst P - z.subst Q) := by sorry
