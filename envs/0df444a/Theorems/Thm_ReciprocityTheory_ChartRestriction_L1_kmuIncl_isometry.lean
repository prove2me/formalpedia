-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kmuIncl_isometry
-- name    : ReciprocityTheory.ChartRestriction.L1.kmuIncl_isometry
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:44:55.161678+00:00
-- url     : https://prove2.me/theorems/528cb390-179c-5805-b6a5-d9ebacc67fac
-- title:
--   L1: kmu Incl isometry
-- statement:
--   The L1 construction uses the kmu Incl isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/KmuInclDenseRange.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/KmuInclDenseRange.lean#L16-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KmuInclDenseRange
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
variable (l : ℕ) [Fact l.Prime]

theorem ReciprocityTheory.ChartRestriction.L1.kmuIncl_isometry : Isometry (kmuIncl l) := by sorry
