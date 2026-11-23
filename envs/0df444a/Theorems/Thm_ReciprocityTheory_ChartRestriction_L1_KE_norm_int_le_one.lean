-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_KE_norm_int_le_one
-- name    : ReciprocityTheory.ChartRestriction.L1.KE.norm_int_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:04.850191+00:00
-- url     : https://prove2.me/theorems/b927aea7-0e34-4948-8c1c-cd461b6c326e
-- title:
--   KE: norm int le one
-- statement:
--   The KE construction uses the norm int le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormLeOneOfIntegralInt.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/NormLeOneOfIntegralInt.lean#L33-L35

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

theorem ReciprocityTheory.ChartRestriction.L1.KE.norm_int_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] (n : ℤ) :
    ‖algebraMap ℤ K n‖ ≤ 1 := by sorry
