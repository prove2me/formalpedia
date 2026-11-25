-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_gauss_bound
-- name    : ReciprocityTheory.ChartRestriction.L1.gauss_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:21:03.234418+00:00
-- url     : https://prove2.me/theorems/53e1207d-d6d9-42cb-84ad-fabf33bf0d7c
-- title:
--   L1: gauss bound
-- statement:
--   The L1 construction uses the gauss bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgGauss.lean#L113-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgGauss.lean#L113-L122

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgGauss
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
open Formalism.L2.Th1
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem ReciprocityTheory.ChartRestriction.L1.gauss_bound {α : Type} (S : Finset α) (x : α → K) (A : PowerSeries K) (hA : IntegralPS A)
    (hA0 : constantCoeff A = 1) (c : K)
    (hG : IntegralPS (C c * ∏ P ∈ S, (A - C (x P) * X ^ 2))) :
    ‖c‖ * ∏ P ∈ S, max 1 ‖x P‖ ≤ 1 := by sorry
