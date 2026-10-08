-- Prove2me | Theorems.Thm_SPHardness_OrderPolytope_numLinExt_eq
-- name    : SPHardness.OrderPolytope.numLinExt_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:10:12.800983+00:00
-- url     : https://prove2.me/theorems/d64f6d3c-58aa-4c74-80f7-ca059e5cb002
-- title:
--   Proof of Lemma 3, p. 11 — linear extensions equal factorial times order-polytope volume
-- statement:
--   Let $P$ be a finite poset with $k=|P|$, let $N(P)$ be its number of linear extensions, and let $V(P)$ be the volume of its order polytope. The identity cited in the proof of Lemma 3 is
--
--   $$
--   N(P)=k!\,V(P).
--   $$
--
--   This is the geometric bridge between the counting problem and volume approximation. The identity is a theorem to be proved, rather than an assumption in the reduction.
--
--   **Formalization Note** Linear extensions use the published `FCP.Order.LinearExtensions` definition: order-preserving bijections from $P$ to the positions $0,\ldots,k-1$.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), p. 11, proof of Lemma 3, citing Brightwell & Winkler [3]. https://optimization-online.org/wp-content/uploads/2015/03/4825.pdf

import Mathlib
import Definitions.Def_SPHardness_OrderPolytope_Model

namespace SPHardness.OrderPolytope

open scoped Nat

/-- The Brightwell–Winkler linear-extension/volume identity quoted in Lemma 3. -/
theorem numLinExt_eq (P : Type) [Fintype P] [PartialOrder P] :
    (numLinExt P : ℝ) = ((Fintype.card P)! : ℝ) * volOrder P := by sorry

end SPHardness.OrderPolytope
