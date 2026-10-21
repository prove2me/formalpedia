-- Prove2me | Theorems.Thm_UniformPatrol_Star_lemma_3_corrected
-- name    : UniformPatrol.Star.lemma_3_corrected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:53.654298+00:00
-- url     : https://prove2.me/theorems/b06d78e2-af2f-4956-9569-863c282aa26c
-- title:
--   Lemma 3, furthermore part corrected — delay two minimizes interception
-- statement:
--   With full reflection $s=1$, an attacker choosing the same end $A$ minimizes interception by using delay two:
--
--   $$Q_{n,m}(p,1;A,2)\leq Q_{n,m}(p,1;A,d)\quad(d\geq1).$$
--
--   If $np<1$, the inequality is strict whenever $d\ne2$, for every $m\geq2$. This gives the attacker's response comparison for the saddle point.
--
--   **Formalization Note** The printed furthermore sentence instead claims unique optimality for odd $m$. At $p=1/n$ and odd $m$, Proposition 2 makes every delay optimal, so that sentence is false. The Lean strict clause uses $np<1$ and covers all durations. The mission also assumes $n\geq2$.
-- source:
--   Alpern, Chleboun, Katsikas, The Uniformed Patroller Game, arXiv:1908.07366v2, p. 10 (PDF 11), Lemma 3 and its proof

import Mathlib
import Definitions.Def_UniformPatrol_Star_Model

namespace UniformPatrol.Star

/-- Lemma 3, with the printed uniqueness claim corrected at the zero-holding boundary. -/
theorem lemma_3_corrected (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (x : PStrat n) (hs : x.s = 1) (a a' : AStrat n)
    (hA : a.A = a'.A) (hd : a.d = 2) :
    Q n m x a ≤ Q n m x a' ∧
    ((n : ℝ) * x.p < 1 → a'.d ≠ 2 → Q n m x a < Q n m x a') := by sorry

end UniformPatrol.Star
