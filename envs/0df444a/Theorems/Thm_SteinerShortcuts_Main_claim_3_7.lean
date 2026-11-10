-- Prove2me | Theorems.Thm_SteinerShortcuts_Main_claim_3_7
-- name    : SteinerShortcuts.Main.claim_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:36:21.177369+00:00
-- url     : https://prove2.me/theorems/444ef07d-a82d-453d-94c8-3f977688bdf5
-- title:
--   Claim 3.7 — a common switch for both parities
-- statement:
--   In the fixed compatible-pair setup, there is a vertex $v$ of $P_{1,2}$ at which both parities switch:
--   $$
--   P_{1,2}[s(P_1),v]\text{ uses odd/even labels }a_1,b_1,\qquad
--   P_{1,2}[v,t(P_2)]\text{ uses odd/even labels }a_2,b_2.
--   $$
--   This is property (Q3). The switching vertex may be either endpoint. No unequal-label assumption is made, so all four equality cases are included.
--
--   Differences from the source:
--   - encoding: the fixed compatible critical pair and the two cross-paths in the standing setup of §3.1 → explicit Admissible L q and PairSetup hypotheses; reason: these expose even L, prime q in [L,2L], source membership, compatibility and both cross-path endpoint conditions; L≥4 fixes the nondegenerate asymptotic regime required in the brief
--   - encoding: a switching vertex of the cross-path → an index j between zero and the path length, with label requirements before and after j; reason: every path vertex is represented, including both endpoints
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), p. 21, Claim 3.7 (PDF p. 23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_TestFunctions

namespace SteinerShortcuts.Main

theorem claim_3_7 (L q : ℕ) (h : Admissible L q) (P Q : CriticalData q)
    (R T : Route Point) (hs : PairSetup L q P Q R T) :
    Q3 P Q R := by sorry

end SteinerShortcuts.Main
