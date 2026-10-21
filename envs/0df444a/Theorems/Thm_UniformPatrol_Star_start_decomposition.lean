-- Prove2me | Theorems.Thm_UniformPatrol_Star_start_decomposition
-- name    : UniformPatrol.Star.start_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:45.37398+00:00
-- url     : https://prove2.me/theorems/d7b8cc15-8627-4368-a516-22b710847e1d
-- title:
--   Proof of Lemma 3 — conditional attack-start decomposition
-- statement:
--   Let $c(d)$ be the conditional probability that the patroller is at $C$ when an attack of delay $d$ begins, given no earlier return to the attacked end $A$. Let $H_C$ and $H_E$ be the probabilities of reaching $A$ during the remaining $m-1$ transitions from $C$ and from any other end $E$. Then
--
--   $$Q_{n,m}(p,s;A,d)=c(d)H_C+(1-c(d))H_E.$$
--
--   This separates the conditional attack-start distribution from the probability of interception after the attack begins.
--
--   **Formalization Note** The source uses $X_1$ for the attack-start state; Lean uses $X_0=C$ at departure and evaluates $m-1$ transitions from the attack-start state. The mission assumes $n\geq2$.
-- source:
--   Alpern, Chleboun, Katsikas, The Uniformed Patroller Game, arXiv:1908.07366v2, p. 6 (PDF 7), text below eq. (8); p. 10 (PDF 11), proof of Lemma 3

import Mathlib
import Definitions.Def_UniformPatrol_Star_Model

namespace UniformPatrol.Star

/-- The interception probability is the conditional mixture of the two possible attack-start states. -/
theorem start_decomposition (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (x : PStrat n) (a : AStrat n) (j : Fin n) (hj : j ≠ a.A) :
    Q n m x a =
      cAt n x.p x.s a.A a.d * hitWithin n x.p x.s a.A none (m - 1) +
      (1 - cAt n x.p x.s a.A a.d) *
        hitWithin n x.p x.s a.A (some j) (m - 1) := by sorry

end UniformPatrol.Star
