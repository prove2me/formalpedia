-- Prove2me | Theorems.Thm_UniformPatrol_Star_lemma_1
-- name    : UniformPatrol.Star.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:54.130977+00:00
-- url     : https://prove2.me/theorems/3daeff44-976f-4ad0-81bb-8a4decf14d62
-- title:
--   Lemma 1 — reflection maximizes interception against delay two
-- statement:
--   Fix $n\geq2$, $m\geq2$, a centre-to-end probability $p$, an attacked end $A$, and delay $d=2$. Among admissible reflection probabilities, full reflection maximizes interception:
--
--   $$Q_{n,m}(p,s;A,2)\leq Q_{n,m}(p,1;A,2).$$
--
--   If $m\geq3$, the inequality is strict for $s<1$. If $m=2$, the two payoffs are equal for every admissible $s$, and there exists an optimal patroller strategy with $s<1$. This is the patroller's response comparison used in Theorem 1.
--
--   **Formalization Note** The paper's attack-start time $X_1$ corresponds to the state after one step from the model's $X_0=C$. The added $n\geq2$ condition ensures the conditioning event is defined.
-- source:
--   Alpern, Chleboun, Katsikas, The Uniformed Patroller Game, arXiv:1908.07366v2, p. 8 (PDF 9), Lemma 1; p. 4 (PDF 5), §2.1

import Mathlib
import Definitions.Def_UniformPatrol_Star_Model

namespace UniformPatrol.Star

/-- Lemma 1: reflection maximizes interception against delay two. -/
theorem lemma_1 (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (x x₁ : PStrat n) (hp : x₁.p = x.p) (hs : x₁.s = 1)
    (a : AStrat n) (hd : a.d = 2) :
    Q n m x a ≤ Q n m x₁ a ∧
    (3 ≤ m → x.s < 1 → Q n m x a < Q n m x₁ a) ∧
    (m = 2 → Q n m x a = Q n m x₁ a) ∧
    (m = 2 → ∃ y : PStrat n, y.s < 1 ∧ IsOptimalP n 2 y) := by sorry

end UniformPatrol.Star
