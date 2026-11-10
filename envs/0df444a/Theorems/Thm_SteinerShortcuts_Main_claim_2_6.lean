-- Prove2me | Theorems.Thm_SteinerShortcuts_Main_claim_2_6
-- name    : SteinerShortcuts.Main.claim_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:35:15.000292+00:00
-- url     : https://prove2.me/theorems/04d8549c-cc1b-41f4-8c67-c55c894301c9
-- title:
--   Claim 2.6 — uniqueness of critical paths
-- statement:
--   For the optimized graph $G_{L,q}$ with even $L\ge4$ and prime $q\in[L,2L]$, every critical path $P\in\mathcal P$ is a path in the graph and the unique path between its endpoints:
--   $$
--   Q:s(P)\leadsto t(P)\text{ in }G_{L,q}\quad\Longrightarrow\quad Q=P.
--   $$
--   This is property (P1), invoked for the optimized construction on printed page 22. It fixes the meaning of each endpoint pair before shortcutting.
--
--   Differences from the source:
--   - encoding: the optimized graph and critical paths of §3.2, with labels in [0,q−1] → the actual finite boxes of integer 21-tuples, Fin q labels, and recursively computed critical vertex sequences; reason: the coordinate order, inclusive bounds, source layer 1 and zero counters are retained; no graph or path property is assumed by the definitions
--   - encoding: paths and subpaths as vertex sequences → a starting vertex and a finite tail list; contiguous subpaths and splicing are equalities of vertex lists; reason: this is a nonempty vertex sequence, with validity imposed separately; paths in a layered DAG have no repeated vertices
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), p. 12, Claim 2.6; applied on p.22 (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_Construction

namespace SteinerShortcuts.Main

/-- Claim 2.6, applied to the optimized construction as on printed p.22. -/
theorem claim_2_6 (L q : ℕ) (h : Admissible L q) :
    P1 (construction L q) (criticalPaths L q) := by sorry

end SteinerShortcuts.Main
