-- Prove2me | Theorems.Thm_SubmodMDP_Policies_lemma_3
-- name    : SubmodMDP.Policies.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:36.556368+00:00
-- url     : https://prove2.me/theorems/1144e7cb-b198-43ac-ad26-32c19a65f6dd
-- title:
--   Lemma 3 — conditioning maps $Q^{(r)}$ into $Q^{(r-1)}$
-- statement:
--   Let $G$ be a layered graph, $r\ge1$, $x\in Q^{(r)}$, and let $w$ be a vertex with $x_w>0$. Then the conditioned point
--   $$x^{|w}_I=\frac{x_{I\cup\{w\}}}{x_w}\qquad(|I|\le r)$$
--   lies in $Q^{(r-1)}$.
--
--   Conditioning on a vertex is the step that Algorithm 1 performs between consecutive blocks; this lemma guarantees that the recursive calls receive feasible inputs, one level lower in the hierarchy.
--
--   Differences from the source:
--   - encoding: x ∈ ℝ^{(V choose ≤ r+1)} → a function on all vertex sets of which only the coordinates with |I| ≤ r+1 are read; reason: coordinates outside the index set are never used by Q^(r), RRR or the linear functions; same instances
--   - generalization: G a layered graph → any layered-graph datum (vertices, layer numbers, arcs) without the well-formedness conditions; reason: Q^(r) and the conditioning are defined for any such datum and the statement does not use well-formedness; it specializes to layered graphs
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), Lemma 3, p. 5 (PDF p. 6)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_Layered

namespace SubmodMDP.Policies

/-- Lemma 3 (PDF p. 6): conditioning a point of `Q^(r)` on a vertex `w` with `x_w > 0` gives a
point of `Q^(r-1)`. -/
theorem lemma_3 (G : LGraph) (r : ℕ) (hr : 1 ≤ r) (x : Finset (Fin G.N) → ℝ)
    (hx : InQ G r x) (w : Fin G.N) (hw : 0 < x {w}) :
    InQ G (r - 1) (cond x w) := by sorry

end SubmodMDP.Policies
