-- Prove2me | Theorems.Thm_SteinerShortcuts_Main_claim_3_2
-- name    : SteinerShortcuts.Main.claim_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:36:05.981671+00:00
-- url     : https://prove2.me/theorems/086137c2-f026-4a80-b6d0-eca6085361d6
-- title:
--   Claim 3.2 — the three label properties imply splicing
-- statement:
--   In the fixed compatible-pair setup, suppose the cross-path $P_{1,2}$ has properties (Q1), (Q2) and (Q3). Then it satisfies the full splicing property:
--   $$
--   P_{1,2}=P_1[s(P_1),v]\circ P_2[v,t(P_2)]
--   $$
--   for a vertex $v$ common to $P_1$ and $P_2$. This is equality of the whole path, rather than an assertion about its direction labels alone.
--
--   Differences from the source:
--   - encoding: the fixed compatible critical pair and the two cross-paths in the standing setup of §3.1 → explicit Admissible L q and PairSetup hypotheses; reason: these expose even L, prime q in [L,2L], source membership, compatibility and both cross-path endpoint conditions; L≥4 fixes the nondegenerate asymptotic regime required in the brief
--   - encoding: paths and subpaths as vertex sequences → a starting vertex and a finite tail list; contiguous subpaths and splicing are equalities of vertex lists; reason: this is a nonempty vertex sequence, with validity imposed separately; paths in a layered DAG have no repeated vertices
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), p. 16, Claim 3.2 (PDF p. 18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_TestFunctions

namespace SteinerShortcuts.Main

theorem claim_3_2 (L q : ℕ) (h : Admissible L q) (P Q : CriticalData q)
    (R T : Route Point) (hs : PairSetup L q P Q R T)
    (hq1 : Q1 P Q R) (hq2 : Q2 P Q R) (hq3 : Q3 P Q R) :
    Splices (P.route L) (Q.route L) R := by sorry

end SteinerShortcuts.Main
