-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_qls1
-- name    : ReciprocityTheory.ChartRestriction.L1.qls1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:46:36.548714+00:00
-- url     : https://prove2.me/theorems/65098f1c-6176-4cff-a2c6-482d70abc84e
-- title:
--   L1: qls1
-- statement:
--   The L1 construction uses the qls1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonA.lean#L193-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonA.lean#L193-L222

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

theorem ReciprocityTheory.ChartRestriction.L1.qls1 (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (z : PowerSeries K)
    (hz0 : constantCoeff z = 0) (hz : IntegralPS (derivative K z)) (P Q : PowerSeries K)
    (hP0 : constantCoeff P = 0) (hQ0 : constantCoeff Q = 0)
    (hP : IntegralPS P) (hQ : IntegralPS Q) (hPQ : DivBy (l : K) (P - Q)) :
    DivBy (l : K) (z.subst P - z.subst Q) := by sorry
