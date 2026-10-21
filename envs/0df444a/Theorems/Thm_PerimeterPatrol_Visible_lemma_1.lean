-- Prove2me | Theorems.Thm_PerimeterPatrol_Visible_lemma_1
-- name    : PerimeterPatrol.Visible.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:50.429467+00:00
-- url     : https://prove2.me/theorems/f1053a5b-9856-4ce3-a7fe-7c8031fd6363
-- title:
--   Lemma 1, p. 5 — with E[N] = c fixed, the least-variance law on {⌊c⌋, ⌈c⌉} maximizes 1 − E[(1 − p)^N]
-- statement:
--   Let $p \in (0, 1]$ and $c > 0$. Let $N$ be the number of patrollers an attack meets, a nonnegative integer-valued random variable, each patroller detecting independently with probability $p$, so the detection probability is $1 - E[(1-p)^N]$.
--
--   1. For every law $(w_n)_{n \ge 0}$ on $\{0, 1, 2, \dots\}$ with mean $\sum_n n\, w_n = c$,
--
--   $$\sum_{n=0}^\infty \bigl(1 - (1 - p)^n\bigr) w_n \;\le\; 1 - (c - \lfloor c \rfloor)(1 - p)^{\lceil c \rceil} - (1 - c + \lfloor c \rfloor)(1 - p)^{\lfloor c \rfloor}.$$
--
--   2. The least-variance law with mean $c$ attains this bound: $N = c$ deterministically if $c$ is an integer, and otherwise $P\{N = \lfloor c \rfloor\} = \lceil c \rceil - c$, $P\{N = \lceil c \rceil\} = c - \lfloor c \rfloor$. It is a probability law with mean $c$, and its detection probability equals the right-hand side above.
--
--   So the maximum of the detection probability over all laws with mean $c$ is the right-hand side, the value (2) with $c = \lambda t$. This is the extremal fact behind Theorem 2: the defender's best possible guarantee is limited by the mean number of patrollers per attack, and the optimal schedule is the one that makes every attack meet the least-variance number.
--
--   **Formalization Note.** The page's "the distribution that maximizes … is the one that has the least variance" is formalized as: the least-variance law is a maximizer. Uniqueness is not claimed, because it fails at $p = 1$: with $c = 1.5$, both $\{1: \tfrac12, 2: \tfrac12\}$ and $\{1: \tfrac34, 3: \tfrac14\}$ give detection probability $1$. The mean is assumed finite and equal to $c$ (`HasSum`).
-- source:
--   Lin, Optimal Patrol of a Perimeter, arXiv:1905.03600v3, p. 5, Lemma 1

import Mathlib
import Definitions.Def_PerimeterPatrol_Visible_Model

namespace PerimeterPatrol.Visible
theorem lemma_1 (p c : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hc : 0 < c) : (∀ w : ℕ → ℝ, (∀ n, 0 ≤ w n) → HasSum w 1 → HasSum (fun n : ℕ => (n : ℝ) * w n) c → ∑' n : ℕ, (1 - (1 - p) ^ n) * w n ≤ valueC c p) ∧ ((∀ n, 0 ≤ twoPoint c n) ∧ HasSum (twoPoint c) 1 ∧ HasSum (fun n : ℕ => (n : ℝ) * twoPoint c n) c ∧ ∑' n : ℕ, (1 - (1 - p) ^ n) * twoPoint c n = valueC c p) := by sorry
end PerimeterPatrol.Visible
