-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_alt_sum_telescope
-- name    : ReciprocityTheory.Coh.alt_sum_telescope
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:59:24.594252+00:00
-- url     : https://prove2.me/theorems/70bd42b8-4c27-47d5-96f7-62d39399656d
-- title:
--   Coh: alt sum telescope
-- statement:
--   The Coh construction uses the alt sum telescope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/RankLen.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/RankLen.lean#L17-L23

import Definitions.Def_ReciprocityTheory_GroupCohomology_TransgressionStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_FinGen
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiberFirstH0Injective
import Definitions.Def_ReciprocityTheory_GroupCohomology_ProdHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_EqZeroOfLe
import Definitions.Def_ReciprocityTheory_GroupCohomology_RankLenA
import Definitions.Def_ReciprocityTheory_GroupCohomology_RankLen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Cx Function TorsionRankLength
open scoped Pointwise
universe u

theorem ReciprocityTheory.Coh.alt_sum_telescope (a : ℕ → ℤ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (a n + a (n + 1)) = a 0 + (-1) ^ N * a (N + 1) := by sorry
