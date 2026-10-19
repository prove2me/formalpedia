-- Prove2me | Theorems.Thm_UniformPatrol_Star_lemma_2
-- name    : UniformPatrol.Star.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:46.338035+00:00
-- url     : https://prove2.me/theorems/07d9ce2f-8a4a-490f-9d27-92cfcaee372c
-- title:
--   Lemma 2 — starting at the centre improves interception
-- statement:
--   Let $A$ be the attacked end, and $E$ any other end. For every admissible $(p,s)$ and duration $m\geq2$, the chance of reaching $A$ during an attack is at least as high when the patroller starts at $C$ as when she starts at $E$:
--
--   $$\Pr(T_A\leq m\mid X_1=E)\leq\Pr(T_A\leq m\mid X_1=C).$$
--
--   Equality holds exactly when $s=1$, $r=1-np=0$, and $m$ is odd. In particular, the comparison is strict for even $m$. This identifies the better attack-start state for the patroller.
--
--   **Formalization Note** The displayed paper event counts the attack-start state as period one. Lean expresses it as reaching $A$ within $m-1$ subsequent transitions. The mission assumes $n\geq2$.
-- source:
--   Alpern, Chleboun, Katsikas, The Uniformed Patroller Game, arXiv:1908.07366v2, p. 9 (PDF 10), Lemma 2 and eq. (13)

import Mathlib
import Definitions.Def_UniformPatrol_Star_Model

namespace UniformPatrol.Star

/-- Lemma 2: an attack beginning at the centre is at least as likely to be intercepted. -/
theorem lemma_2 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (x : PStrat n) (A j : Fin n) (hj : j ≠ A) :
    hitWithin n x.p x.s A (some j) (m - 1) ≤
      hitWithin n x.p x.s A none (m - 1) ∧
    (hitWithin n x.p x.s A (some j) (m - 1) =
      hitWithin n x.p x.s A none (m - 1) ↔
      x.s = 1 ∧ (n : ℝ) * x.p = 1 ∧ Odd m) := by sorry

end UniformPatrol.Star
