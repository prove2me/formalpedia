-- Prove2me | Theorems.Thm_SuttonBartoRL_FiniteMDP_return_recursion
-- name    : SuttonBartoRL.FiniteMDP.return_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T03:31:26.831634+00:00
-- url     : https://prove2.me/theorems/3d0414a8-d705-4924-bdec-906493dd058c
-- title:
--   Eq. (3.9): the return recursion $G_t = R_{t+1} + \gamma G_{t+1}$
-- statement:
--   Let $0 \le \gamma < 1$ and let $R_1, R_2, \dots$ be a bounded sequence of real rewards, $|R_k| \le C$ for all $k$. For every time step $t$ the discounted return $G_t = \sum_{k=0}^\infty \gamma^k R_{t+k+1}$ is a convergent series, and returns at successive time steps satisfy
--   $$G_t = R_{t+1} + \gamma\, G_{t+1}.$$
--
--   This recursion is what makes the Bellman equations of the chapter possible; it is used in the derivations of (3.14) and (3.18).
--
--   **Formalization Note** The book allows $0 \le \gamma \le 1$ and episodic returns with $G_T = 0$; the statement covers the continuing discounted case $0 \le \gamma < 1$ with bounded rewards, the case in which the book says the infinite sum (3.8) is finite (p. 55). The reward sequence is indexed by $\mathbb N$ and its value at index $0$ is not used.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (3.8)–(3.9), p. 55

import Mathlib
import Definitions.Def_SuttonBartoRL_FiniteMDP_MDP

namespace SuttonBartoRL.FiniteMDP

/-- Sutton & Barto, 2nd ed., Eqs. (3.8)–(3.9), p. 55: for `0 ≤ γ < 1` and a bounded reward sequence
`R_1, R_2, …`, the discounted return `G_t = Σ_{k=0}^∞ γ^k R_{t+k+1}` is a convergent series and
satisfies `G_t = R_{t+1} + γ G_{t+1}` for every `t`. -/
theorem return_recursion (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (R : ℕ → ℝ)
    (hR : ∃ C : ℝ, ∀ k, |R k| ≤ C) (t : ℕ) :
    Summable (fun k : ℕ => γ ^ k * R (t + k + 1)) ∧
      discountedReturn γ R t = R (t + 1) + γ * discountedReturn γ R (t + 1) := by sorry

end SuttonBartoRL.FiniteMDP
