-- Prove2me | Theorems.Thm_UniformPatrol_Star_even_interior
-- name    : UniformPatrol.Star.even_interior
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:54.274128+00:00
-- url     : https://prove2.me/theorems/aea67f1a-908a-4c68-b154-ec9452098e9e
-- title:
--   §2.6, p. 15 — an interior maximizer for even durations
-- statement:
--   For every even attack duration $m\geq2$ and $n\geq2$, there is an admissible full-reflection strategy $(p,1)$ with positive holding probability $r=1-np>0$ that maximizes interception against delay two among all admissible full-reflection strategies:
--
--   $$Q_{n,m}(p',1;A,2)\leq Q_{n,m}(p,1;A,2)\quad\text{for every admissible }p'.$$
--
--   The interior condition supports the even-duration uniqueness of delay two.
--
--   **Formalization Note** The preprint reports interior maxima for even $m$ in its Figure 2 discussion, but does not supply an analytic proof for all $n,m$. The theorem formalizes this stated observation. The attacked end is arbitrary by symmetry.
-- source:
--   Alpern, Chleboun, Katsikas, The Uniformed Patroller Game, arXiv:1908.07366v2, p. 15 (PDF 16), §2.6 and Figure 2 discussion

import Mathlib
import Definitions.Def_UniformPatrol_Star_Model

namespace UniformPatrol.Star

/-- The even-duration optimum has positive holding probability at the centre. -/
theorem even_interior (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (he : Even m) :
    ∃ x : PStrat n, x.s = 1 ∧ (n : ℝ) * x.p < 1 ∧
      ∀ x' : PStrat n, x'.s = 1 → ∀ a : AStrat n, a.d = 2 →
        Q n m x' a ≤ Q n m x a := by sorry

end UniformPatrol.Star
