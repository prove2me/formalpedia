-- Prove2me | Theorems.Thm_UniformPatrol_Star_symmetry
-- name    : UniformPatrol.Star.symmetry
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:44.322718+00:00
-- url     : https://prove2.me/theorems/b39a0ebc-4711-40fb-a166-60e941b49e6a
-- title:
--   Figure 1 — symmetry of the attacked end node
-- statement:
--   For any admissible patroller strategy $(p,s)$, duration $m\geq2$, and two attacks on the star with the same delay $d$, the interception probability is independent of which end node is attacked:
--
--   $$Q_{n,m}(p,s;A,d)=Q_{n,m}(p,s;A',d).$$
--
--   This permits reducing the original $n+1$-node chain to the centre, the attacked end, and the other ends when analyzing the payoff.
--
--   **Formalization Note** The star itself remains the model; the symmetry is a theorem. The mission assumes $n\geq2$.
-- source:
--   Alpern, Chleboun, Katsikas, The Uniformed Patroller Game, arXiv:1908.07366v2, p. 3 (PDF 4), Figure 1 and §2

import Mathlib
import Definitions.Def_UniformPatrol_Star_Model

namespace UniformPatrol.Star

/-- Figure 1: the attacked end node's label does not change the payoff. -/
theorem symmetry (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (x : PStrat n) (a a' : AStrat n) (hd : a.d = a'.d) :
    Q n m x a = Q n m x a' := by sorry

end UniformPatrol.Star
