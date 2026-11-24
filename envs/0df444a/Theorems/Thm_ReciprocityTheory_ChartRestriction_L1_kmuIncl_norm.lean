-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kmuIncl_norm
-- name    : ReciprocityTheory.ChartRestriction.L1.kmuIncl_norm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:00:52.270681+00:00
-- url     : https://prove2.me/theorems/faa4df39-0049-47f2-b93e-e7f560bb7d6e
-- title:
--   L1: kmu Incl norm
-- statement:
--   The L1 construction uses the kmu Incl norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/KmuInclDenseRange.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/KmuInclDenseRange.lean#L14-L14

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

theorem ReciprocityTheory.ChartRestriction.L1.kmuIncl_norm (x : Kmu l) : ‖kmuIncl l x‖ = ‖x‖ := by sorry
