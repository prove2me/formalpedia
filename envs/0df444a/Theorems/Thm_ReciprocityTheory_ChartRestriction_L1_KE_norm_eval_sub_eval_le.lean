-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KE_norm_eval_sub_eval_le
-- name    : ReciprocityTheory.ChartRestriction.L1.KE.norm_eval_sub_eval_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:34.207048+00:00
-- url     : https://prove2.me/theorems/b6a9b1b7-83de-5ecc-9bd0-0d302a68e858
-- title:
--   KE: norm eval sub eval le
-- statement:
--   The KE construction uses the norm eval sub eval le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormLeOneOfIntegralInt.lean#L57-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormLeOneOfIntegralInt.lean#L57-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsTeichmullerRepModPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_NormLeOneOfIntegralInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1 ReciprocityTheory.ChartRestriction.L1.KE
open Formalism.L2.Th1.CM

theorem ReciprocityTheory.ChartRestriction.L1.KE.norm_eval_sub_eval_le {K : Type*} [NormedField K] [IsUltrametricDist K] (P : Polynomial K)
    (hP : ∀ i, ‖P.coeff i‖ ≤ 1) {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖P.eval x - P.eval y‖ ≤ ‖x - y‖ := by sorry
