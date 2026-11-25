-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_RankA_col_mem_range
-- name    : ReciprocityTheory.PGsh.Up.RankA.col_mem_range
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:06:30.148014+00:00
-- url     : https://prove2.me/theorems/381e2aec-c973-5ad0-b6f2-150c76367506
-- title:
--   Rank A: col mem range
-- statement:
--   The Rank A construction uses the col mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RankMapLeRank.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RankMapLeRank.lean#L11-L13

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

theorem ReciprocityTheory.PGsh.Up.RankA.col_mem_range {m n : Type} [Fintype n] [DecidableEq n] (A : Matrix m n S) (y : n) :
    (fun x => A x y) ∈ LinearMap.range A.mulVecLin := by sorry
