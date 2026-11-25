-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_RankA_sum_finrank
-- name    : ReciprocityTheory.PGsh.Up.RankA.sum_finrank
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:14.164028+00:00
-- url     : https://prove2.me/theorems/a19a7f3f-eba7-48d8-9da9-edc007e912d5
-- title:
--   Rank A: sum finrank
-- statement:
--   The Rank A construction uses the sum finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RankMapLeRank.lean#L40-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RankMapLeRank.lean#L40-L69

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

theorem ReciprocityTheory.PGsh.Up.RankA.sum_finrank {ι m : Type} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]
    [StrongRankCondition S] (e : m → Matrix ι ι S)
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (hsum : ∑ i, e i = 1)
    [∀ i, Module.Free S (LinearMap.range (e i).mulVecLin)]
    [∀ i, Module.Finite S (LinearMap.range (e i).mulVecLin)] :
    ∑ i, Module.finrank S (LinearMap.range (e i).mulVecLin) = Fintype.card ι := by sorry
