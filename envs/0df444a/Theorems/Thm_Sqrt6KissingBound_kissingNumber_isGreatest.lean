-- Prove2me | Theorems.Thm_Sqrt6KissingBound_kissingNumber_isGreatest
-- name    : Sqrt6KissingBound.kissingNumber_isGreatest
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T06:10:33.356667+00:00
-- url     : https://prove2.me/theorems/e9742176-6bb7-58c7-a0a5-0024286d823d
-- title:
--   Sqrt6 Kissing Bound: kissing Number is Greatest
-- statement:
--   The Sqrt6 Kissing Bound construction uses the kissing Number is Greatest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/KissingNumber.lean#L54-L58
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/KissingNumber.lean#L54-L58

import Definitions.Def_Sqrt6KissingBound_Optimality
import Mathlib.Data.Nat.Find
import Definitions.Def_Sqrt6KissingBound_KissingNumber
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section

theorem Sqrt6KissingBound.kissingNumber_isGreatest {n : ℕ} (hn : 1 ≤ n) :
    IsGreatest {m : ℕ | RealizableKissingCard n m} (kissingNumber n) := by sorry
