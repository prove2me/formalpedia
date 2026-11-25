-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_RankA_rank_map_le
-- name    : ReciprocityTheory.PGsh.Up.RankA.rank_map_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:40.699109+00:00
-- url     : https://prove2.me/theorems/362ec852-4c75-4ec2-9306-8c2e86a9c499
-- title:
--   Rank A: rank map le
-- statement:
--   The Rank A construction uses the rank map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RankMapLeRank.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RankMapLeRank.lean#L28-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RankMapLeRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.RankA
variable {S : Type} [CommRing S]

theorem ReciprocityTheory.PGsh.Up.RankA.rank_map_le [StrongRankCondition S] {K : Type} [Field K] (f : S →+* K) {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n S) [Module.Free S (LinearMap.range A.mulVecLin)]
    [Module.Finite S (LinearMap.range A.mulVecLin)] :
    (A.map f).rank ≤ Module.finrank S (LinearMap.range A.mulVecLin) := by sorry
