-- Prove2me | Theorems.Thm_RandomLeadGBS_Diffusion_theorem_1_stability
-- name    : RandomLeadGBS.Diffusion.theorem_1_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:09.208031+00:00
-- url     : https://prove2.me/theorems/8724fb05-efa0-472d-87b2-cca277f5e656
-- title:
--   Theorem 1 (stability part), p. 10 — the GBS chain has a single closed class reached from every state and, for large r, a unique stationary distribution
-- statement:
--   Assume the standing assumptions: $\beta>0$, an integer $\gamma\ge 1$, $f(r)>0$, $f(r)/r\to 0$ and $f(r)/\sqrt r\to\infty$, with arbitrary centering $x_*(r)$. Consider the GBS chain $(Y^r, Z^r)$ on $\mathbb Z\times\mathbb Z_+$ with customer rate $r$ and item rate $\beta Z$. Then:
--
--   1. for every $r>0$ there is a state $s_0$ that is reachable, through a finite sequence of positive-rate jumps, from every state;
--   2. there is $r_0$ such that for every $r\ge r_0$ the chain has exactly one stationary distribution.
--
--   This is the stability statement of Theorem 1: positive recurrence and uniqueness of the stationary regime for all sufficiently large $r$, which every limit statement about $Y^r(\infty)$ presupposes.
--
--   **Formalization Note** The page says the chain is irreducible. On the full lattice $\mathbb Z\times\mathbb Z_+$ that is false: a state with $Z<\lceil T(Y)\rceil$ is never entered, because the policy restores $Z\ge\lceil T\rceil$ after every arrival. Clause 1 states what holds and what uniqueness rests on: one state is accessible from all states, so there is a single closed communicating class. Positive recurrence is expressed as existence of a stationary distribution (global balance with finite mean exit rate).
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, p. 10, Theorem 1 (first sentence); proof sketch pp. 12–13

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

namespace RandomLeadGBS.Diffusion

theorem theorem_1_stability (P : Params) (hP : P.Standing) :
    (∀ r : ℝ, 0 < r → ∃ s₀ : State, ∀ s : State, Relation.ReflTransGen (Step P r) s s₀) ∧
    (∃ r₀ : ℝ, ∀ r ≥ r₀, ∃! p : State → ℝ, IsStationary P r p) := by sorry

end RandomLeadGBS.Diffusion
