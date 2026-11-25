-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kmuIncl_denseRange
-- name    : ReciprocityTheory.ChartRestriction.L1.kmuIncl_denseRange
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:46:07.660841+00:00
-- url     : https://prove2.me/theorems/b616d349-582a-57ab-a4d3-98bd8c5387a0
-- title:
--   L1: kmu Incl dense Range
-- statement:
--   The L1 construction uses the kmu Incl dense Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/KmuInclDenseRange.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/KmuInclDenseRange.lean#L19-L24

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

theorem ReciprocityTheory.ChartRestriction.L1.kmuIncl_denseRange : DenseRange (kmuIncl l) := by sorry
