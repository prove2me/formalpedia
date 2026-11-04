-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalTupleWantedLookup_wanted_lookup
-- name    : ThreeSum.WeightedGlobalTupleWantedLookup.wanted_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:02:42.147341+00:00
-- url     : https://prove2.me/theorems/e1f0c366-fbb5-432a-a388-4683697b06dc
-- title:
--   Weighted Global Tuple Wanted Lookup: wanted lookup
-- statement:
--   A retained output tuple is really traversed by the literal wanted DFS.
--   The returned word and bank IDs use exactly the aligned local array indices.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleWantedLookup.lean#L49-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryTupleWantedLookup.lean#L49-L71

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleDictionaryLookup
import Definitions.Def_Submission_Weighted_Global_TernaryTupleWantedLookup
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTupleWantedLookup
open TernaryWantedLittleEndian
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalTupleWantedLookup.wanted_lookup {A : Type*} (base xs : List A) (r : ℕ)
    (hx : xs∈RadixKeyLists.tuples base r) (p : ℕ) (hp : p≠0)
    (raw : A→ℤ) (word group : A→ℕ) (R F : ℕ) (x : ℤ)
    (hdiv : (p : ℤ)^r∣x-Radix.positionalHash (p : ℤ) raw xs) :
    (Nat.ofDigits R (xs.map word),Nat.ofDigits F (xs.map group))∈
      wantedCodes (p : ℤ) (base.map raw) (base.map word) (base.map group) r x R F 0 1 0 1 := by sorry
