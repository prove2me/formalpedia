-- Prove2me | Theorems.Thm_SteinerShortcuts_Main_claim_3_8
-- name    : SteinerShortcuts.Main.claim_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:36:26.854385+00:00
-- url     : https://prove2.me/theorems/598a8bd7-119e-4822-88ee-b51b894b4fe8
-- title:
--   Claim 3.8 — every cross-path splices
-- statement:
--   Let $P_1,P_2$ be any compatible critical pair in the optimized construction. Every path $P_{1,2}$ from $s(P_1)$ to $t(P_2)$ satisfies
--   $$
--   \exists v\in P_1\cap P_2,\qquad P_{1,2}=P_1[s(P_1),v]\circ P_2[v,t(P_2)].
--   $$
--   Thus the construction has (P2′). Compatibility includes the reverse reachability condition, but no particular reverse cross-path is assumed or chosen in the conclusion. Equal labels remain allowed.
--
--   Differences from the source:
--   - encoding: the optimized graph and critical paths of §3.2, with labels in [0,q−1] → the actual finite boxes of integer 21-tuples, Fin q labels, and recursively computed critical vertex sequences; reason: the coordinate order, inclusive bounds, source layer 1 and zero counters are retained; no graph or path property is assumed by the definitions
--   - encoding: paths and subpaths as vertex sequences → a starting vertex and a finite tail list; contiguous subpaths and splicing are equalities of vertex lists; reason: this is a nonempty vertex sequence, with validity imposed separately; paths in a layered DAG have no repeated vertices
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), p. 21, Claim 3.8 (PDF p. 23); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_TestFunctions

namespace SteinerShortcuts.Main

theorem claim_3_8 (L q : ℕ) (h : Admissible L q) (P Q : CriticalData q)
    (hp : P.Valid L) (hq : Q.Valid L)
    (hc : CompatiblePair (construction L q) (P.route L) (Q.route L))
    (R : Route Point) (hr : IsCrossPath (construction L q) (P.route L) (Q.route L) R) :
    Splices (P.route L) (Q.route L) R := by sorry

end SteinerShortcuts.Main
