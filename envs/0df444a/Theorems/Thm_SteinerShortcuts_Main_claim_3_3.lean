-- Prove2me | Theorems.Thm_SteinerShortcuts_Main_claim_3_3
-- name    : SteinerShortcuts.Main.claim_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:36:12.178567+00:00
-- url     : https://prove2.me/theorems/eb01bdeb-6961-49d9-849d-6425b2f654a5
-- title:
--   Claim 3.3 — two possible labels for each parity
-- statement:
--   In the fixed compatible-pair setup, let $a_i,b_i$ be the odd and even labels of critical path $P_i$. At every step of either cross-path,
--   $$
--   \text{odd label}\in\{a_1,a_2\},\qquad \text{even label}\in\{b_1,b_2\}.
--   $$
--   This is (Q1) on both $P_{1,2}$ and $P_{2,1}$, including the equal-label cases. It restricts every actual edge of these paths.
--
--   Differences from the source:
--   - encoding: the fixed compatible critical pair and the two cross-paths in the standing setup of §3.1 → explicit Admissible L q and PairSetup hypotheses; reason: these expose even L, prime q in [L,2L], source membership, compatibility and both cross-path endpoint conditions; L≥4 fixes the nondegenerate asymptotic regime required in the brief
--   - encoding: a step direction and its label → the difference of the first position-sum coordinate at the two edge endpoints; reason: directions have first coordinate t, making this the actual label on every construction edge
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), p. 17, Claim 3.3 (PDF p. 19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_TestFunctions

namespace SteinerShortcuts.Main

theorem claim_3_3 (L q : ℕ) (h : Admissible L q) (P Q : CriticalData q)
    (R T : Route Point) (hs : PairSetup L q P Q R T) :
    Q1 P Q R ∧ Q1 Q P T := by sorry

end SteinerShortcuts.Main
