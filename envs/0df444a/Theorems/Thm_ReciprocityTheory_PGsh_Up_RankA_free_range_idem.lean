-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_RankA_free_range_idem
-- name    : ReciprocityTheory.PGsh.Up.RankA.free_range_idem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:07:11.145146+00:00
-- url     : https://prove2.me/theorems/ba4e3829-1a2e-488a-a897-d57a34728c9c
-- title:
--   Rank A: free range idem
-- statement:
--   The Rank A construction uses the free range idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RankMapLeRank.lean#L71-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RankMapLeRank.lean#L71-L83

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

theorem ReciprocityTheory.PGsh.Up.RankA.free_range_idem [IsLocalRing S] {ι : Type} [Fintype ι] [DecidableEq ι] (e : Matrix ι ι S)
    (he : e * e = e) :
    Module.Free S (LinearMap.range e.mulVecLin) ∧ Module.Finite S (LinearMap.range e.mulVecLin) := by sorry
