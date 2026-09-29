-- Prove2me | Theorems.Thm_VectorPayoffs_Convex_convex_blackwell_condition
-- name    : VectorPayoffs.Convex.convex_blackwell_condition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:09:59.836213+00:00
-- url     : https://prove2.me/theorems/2e06ff72-6808-452c-afc9-45bf474aa69c
-- title:
--   Proof of THEOREM 3, first paragraph — a closed convex S meeting every T(q) satisfies THEOREM 1's hypothesis
-- statement:
--   Let $M$ be an $r\times s$ vector-payoff game with $r,s\ge1$, and let $S\subseteq\mathbb R^N$ be closed and convex with $S\cap T(q)\neq\emptyset$ for every $q\in Q$. Then for every $x\notin S$ there is $p\in P$ and a point $y\in S$ closest to $x$ such that
--   $$\langle x-y,\;w-y\rangle\le0\qquad\text{for all }w\in R(p),$$
--   i.e. the hyperplane through $y$ perpendicular to $xy$ separates $x$ from $R(p)$.
--
--   Together with THEOREM 1 this gives the "if" direction of THEOREM 3.
--
--   **Formalization Note** The statement is pointwise in $x$; no measurable selection of $p$ is asserted. $r,s\ge1$ is added: with $s=0$ the hypothesis on $T(q)$ is vacuous and $S=\emptyset$ would be a counterexample.
-- source:
--   Blackwell, An analog of the minimax theorem for vector payoffs, Pacific J. Math. 6(1), 1956, p. 6, §3, proof of THEOREM 3, first paragraph

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game

open MeasureTheory

namespace VectorPayoffs.Convex

/-- Blackwell (1956), §3, proof of THEOREM 3, p. 6, first paragraph: a closed convex `S` meeting
every `T(q)` satisfies the hypothesis of THEOREM 1 at every point `x ∉ S`. -/
theorem convex_blackwell_condition {N r s : ℕ} (G : Game N r s) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (S : Set (E N)) (hS : IsClosed S) (hSc : Convex ℝ S)
    (hT : ∀ q ∈ stdSimplex ℝ (Fin s), (S ∩ G.T q).Nonempty) :
    ∀ x ∉ S, ∃ p ∈ stdSimplex ℝ (Fin r), G.BlackwellCondition S p x := by sorry

end VectorPayoffs.Convex
