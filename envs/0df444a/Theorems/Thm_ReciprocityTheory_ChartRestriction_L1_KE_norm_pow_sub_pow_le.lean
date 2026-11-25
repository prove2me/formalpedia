-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KE_norm_pow_sub_pow_le
-- name    : ReciprocityTheory.ChartRestriction.L1.KE.norm_pow_sub_pow_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:50.441827+00:00
-- url     : https://prove2.me/theorems/6db7aaf7-4c6c-4d23-a02a-79921b32f7be
-- title:
--   KE: norm pow sub pow le
-- statement:
--   The KE construction uses the norm pow sub pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormLeOneOfIntegralInt.lean#L41-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormLeOneOfIntegralInt.lean#L41-L55

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

theorem ReciprocityTheory.ChartRestriction.L1.KE.norm_pow_sub_pow_le {K : Type*} [NormedField K] [IsUltrametricDist K] {x y : K}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (i : ℕ) : ‖x ^ i - y ^ i‖ ≤ ‖x - y‖ := by sorry
