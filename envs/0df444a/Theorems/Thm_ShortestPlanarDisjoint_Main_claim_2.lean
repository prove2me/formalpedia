-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_claim_2
-- name    : ShortestPlanarDisjoint.Main.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:54.341712+00:00
-- url     : https://prove2.me/theorems/016add17-e5b0-4a10-8fe2-7ba43208204b
-- title:
--   Claim 2 — Cycle contribution
-- statement:
--   Fix a simple cycle with $h\ge3$ vertices and edge transports $T_1,\ldots,T_h$
--   in one traversal order. Omit the common cost factor. At each vertex choose an
--   incoming port and use the other outgoing port. Summing the products of all edge
--   weights over these assignments gives
--
--   $$\sum_{\text{port assignments}}\operatorname{weight}
--     =\operatorname{tr}(T_1\cdots T_h).$$
--
--   Every assignment is counted once. The reverse traversal is not a second summand.
--   A doubled edge is excluded from this calculation, exactly as in the source; its
--   two distinct matchings require a determinant calculation instead.
--
--   Differences from the source:
--   - generalization: Laurent transport matrices over F₂ and its extensions → arbitrary 2×2 edge matrices over any commutative ring of characteristic two; reason: the trace identity is a local port contraction and specializes to all source transports without extra assumptions
--   - encoding: a fixed simple cycle in a simple graph → h≥3 cyclically indexed distinct component vertices, with one binary port choice per vertex; reason: a simple undirected cycle has at least three vertices; the matrix identity is independent of vertex names or the surrounding graph
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Claim 2, p. 22 (PDF p. 24)

import Definitions.Def_ShortestPlanarDisjoint_Main_PortContributions

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main

/-- Every port assignment for the fixed undirected simple cycle is counted once;
no second term for the opposite traversal direction is added. -/
theorem claim_2 {R : Type*} [CommRing R] [CharP R 2] {h : ℕ}
    (hh : 3 ≤ h) (ts : Fin h → Mat2 R) :
    cyclePortSum (by omega : 0 < h) ts =
      Matrix.trace (transport (List.ofFn ts)) := by sorry

end ShortestPlanarDisjoint.Main
