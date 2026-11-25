-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_semilin_norm_sub_le
-- name    : ReciprocityTheory.ChartRestriction.L1.semilin_norm_sub_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:46:36.288044+00:00
-- url     : https://prove2.me/theorems/2174ba67-23e6-4083-8044-d0c12d8197e8
-- title:
--   L1: semilin norm sub le
-- statement:
--   The L1 construction uses the semilin norm sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/SemilinNormPowSubPow.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/SemilinNormPowSubPow.lean#L17-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SemilinNormPowSubPow
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
open Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]
omit [CompleteSpace K] [CharZero K]

theorem ReciprocityTheory.ChartRestriction.L1.semilin_norm_sub_le {a b : K} {t : ℝ} (ha : ‖a‖ ≤ t) (hb : ‖b‖ ≤ t) : ‖a - b‖ ≤ t := by sorry
