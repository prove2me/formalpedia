-- Prove2me | Theorems.Thm_ThreeSum_WeightedFrozenQueryCost_caps_update
-- name    : ThreeSum.WeightedFrozenQueryCost.caps_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:13:38.701002+00:00
-- url     : https://prove2.me/theorems/6d585dd7-549f-44d2-9007-743533c61fbc
-- title:
--   Weighted Frozen Query Cost: caps update
-- statement:
--   The Weighted Frozen Query Cost construction uses the caps update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L58-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L58-L64

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenQueryCost
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration

theorem ThreeSum.WeightedFrozenQueryCost.caps_update {N : ℕ} (coords : List (Fin N)) (R : Word N) (i : Fin N)
    (d : Fin 3) (hi : i ∉ coords) :
    caps coords (Function.update R i d)=caps coords R := by sorry
