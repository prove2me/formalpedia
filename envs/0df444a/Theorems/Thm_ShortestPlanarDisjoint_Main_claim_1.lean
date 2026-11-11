-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_claim_1
-- name    : ShortestPlanarDisjoint.Main.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:57.154203+00:00
-- url     : https://prove2.me/theorems/e9860b45-7230-4caa-b178-567d79aded54
-- title:
--   Claim 1 — Path contribution
-- statement:
--   Let a fixed path run from terminal $i$ to terminal $j$, with edge transports
--   $T_1,\ldots,T_{h+1}$ in traversal order and terminal vectors $v_i=(t_i,1)^T$,
--   $v_j=(t_j,1)^T$. Omit its common cost factor, as in the source. Sum the products
--   of the edge-block weights over all assignments of distinct incoming and outgoing
--   ports at its $h$ internal vertices. Then
--
--   $$\sum_{\text{port assignments}}\operatorname{weight}
--     =[v_i,T_1\cdots T_{h+1}v_j].$$
--
--   This includes a single-edge path ($h=0$), for which there is no internal port
--   choice. It identifies the entire cost-free contribution of a fixed path in the
--   port expansion.
--
--   Differences from the source:
--   - generalization: Laurent transport matrices and independent terminal variables over F₂ and its extensions → arbitrary 2×2 edge matrices and arbitrary terminal scalars over any commutative ring of characteristic two; reason: the local identity needs neither determinant one, a specific crossing factorization, nor algebraically independent terminal scalars; the source Laurent ring, transports and terminal indeterminates are allowed instances
--   - encoding: h edges in the source path traversal → h+1 edges indexed by Fin(h+1), with h internal port choices; reason: this represents exactly all nonempty terminal-terminal paths, including a single edge; the common cost factor is omitted in both statements
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Claim 1, p. 21 (PDF p. 23)

import Definitions.Def_ShortestPlanarDisjoint_Main_PortContributions

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main

/-- The omitted common z-cost factor is exactly the convention before Claim 1.
The algebraic identity holds for every characteristic-two commutative ring and
all edge matrices, and in particular for the source's Laurent edge transports. -/
theorem claim_1 {R : Type*} [CommRing R] [CharP R 2] {h : ℕ}
    (ts : Fin (h + 1) → Mat2 R) (ti tj : R) :
    pathPortSum ts (terminalVector ti) (terminalVector tj) =
      bracket (terminalVector ti)
        ((transport (List.ofFn ts)).mulVec (terminalVector tj)) := by sorry

end ShortestPlanarDisjoint.Main
