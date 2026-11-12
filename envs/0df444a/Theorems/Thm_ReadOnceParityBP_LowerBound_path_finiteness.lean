-- Prove2me | Theorems.Thm_ReadOnceParityBP_LowerBound_path_finiteness
-- name    : ReadOnceParityBP.LowerBound.path_finiteness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:24:54.956638+00:00
-- url     : https://prove2.me/theorems/d06c002d-823b-47c2-8a35-6bf1a6dcd879
-- title:
--   Finite path sets in acyclic programs
-- statement:
--   For any finite labelled acyclic multigraph G with designated terminals s,t, its edge-list path set is finite:
--
--   $$\#\{p:s\leadsto t\}<\infty.$$
--
--   This ensures that parity cardinality and the algebraic path sum have their intended finite meanings, including parallel edges and the empty path.
--
--   Differences from the source:
--   - encoding: finite variable sets and finite directed acyclic multigraphs → finite numbered vertices and edges, with edge-list walks and possibly equal terminals; reason: numbering preserves parallel edges, dead edges, and every finite graph; the empty path is retained
--   - generalization: Boolean and algebraic edge-label alphabets → any edge-label type; reason: walk finiteness depends only on the finite acyclic graph and does not inspect its labels
-- source:
--   Ben Lee Volk, STOC 2027 submission #132 (October 2026), Definitions 1.1 and 2.1, pp.2–3 (implicit finiteness of the path sums); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/132.pdf

import Mathlib
import Definitions.Def_ReadOnceParityBP_LowerBound_LabelledDAG

set_option autoImplicit false

namespace ReadOnceParityBP.LowerBound

/-- Definitions 1.1 and 2.1: acyclicity makes the actual edge-path set finite.
This is a proof obligation, not a finiteness certificate stored in the graph. -/
theorem path_finiteness {L : Type} (G : LabelledDAG L) :
    G.stPaths.Finite := by sorry

end ReadOnceParityBP.LowerBound
