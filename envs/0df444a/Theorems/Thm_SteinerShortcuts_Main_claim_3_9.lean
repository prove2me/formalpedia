-- Prove2me | Theorems.Thm_SteinerShortcuts_Main_claim_3_9
-- name    : SteinerShortcuts.Main.claim_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:35:17.406049+00:00
-- url     : https://prove2.me/theorems/d3832276-513d-4357-a1ee-060b827c3e8e
-- title:
--   Claim 3.9 — uniqueness and overlap for all critical subpaths
-- statement:
--   Let $\mathcal P'$ be any finite family of contiguous subpaths of critical paths in the optimized construction. Then
--   $$
--   \text{(P1) and (P2) hold for }\mathcal P'.
--   $$
--   Every member is the unique path between its own endpoints, and any two compatible members share a vertex. The subpaths may begin and end at arbitrary layers, may have different lengths, and may have length zero. No extra nonemptiness assumption is placed on the family.
--
--   Differences from the source:
--   - encoding: the optimized graph and critical paths of §3.2, with labels in [0,q−1] → the actual finite boxes of integer 21-tuples, Fin q labels, and recursively computed critical vertex sequences; reason: the coordinate order, inclusive bounds, source layer 1 and zero counters are retained; no graph or path property is assumed by the definitions
--   - encoding: paths and subpaths as vertex sequences → a starting vertex and a finite tail list; contiguous subpaths and splicing are equalities of vertex lists; reason: this is a nonempty vertex sequence, with validity imposed separately; paths in a layered DAG have no repeated vertices
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), p. 23, Claim 3.9 (PDF p. 25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_Construction

namespace SteinerShortcuts.Main

theorem claim_3_9 (L q : ℕ) (h : Admissible L q) (subpaths : Finset (Route Point))
    (hs : ∀ R ∈ subpaths, ∃ P ∈ criticalPaths L q, IsSubpath R P) :
    P1 (construction L q) subpaths ∧ P2 (construction L q) subpaths := by sorry

end SteinerShortcuts.Main
