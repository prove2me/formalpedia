-- Prove2me | Theorems.Thm_SerfozoStochasticNetworks_timeReversal_stationary
-- name    : SerfozoStochasticNetworks.timeReversal_stationary
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-19T02:52:02.486514+00:00
-- url     : https://prove2.me/theorems/39acc0e5-75e9-4de0-a1e5-a31df372e3db
-- title:
--   Theorem 2.5 — identifying a stationary distribution from the reversed rates
-- statement:
--   Let $q$ and $\bar q$ be rate functions on a state space and let $\pi$ be strictly positive.
--   Suppose the families $y\mapsto q(x,y)$, $y\mapsto\bar q(x,y)$ and $y\mapsto\pi(y)q(y,x)$ are
--   summable for every $x$, and that
--
--   * $\bar q(x,y)=\pi(x)^{-1}\pi(y)\,q(y,x)$ for all $x,y$, and
--   * $\sum_y q(x,y)=\sum_y\bar q(x,y)$ for every $x$ — the two rate functions have the same total
--     exit rate from each state.
--
--   Then $\pi$ is an invariant measure of $q$:
--   $$\pi(x)\sum_y q(x,y)=\sum_y\pi(y)q(y,x)\qquad\text{for every }x .$$
--
--   This is a way to find an equilibrium measure by *guessing the time-reversed process*: propose a
--   $\bar q$ and a $\pi$, check the two displayed conditions, and the balance equations come for
--   free. Reversibility is not involved — $\bar q$ need not equal $q$.
--
--   **Formalization Note** The conclusion is the balance equations, which is the content of the
--   book's proof. Calling $\pi$ "the stationary distribution" additionally requires it to be
--   normalized and the process to be ergodic, neither of which is an algebraic consequence of the
--   hypotheses; and the statement that $\bar q$ is the rate function of a time reversal requires
--   the process to be constructed, which is not done here.
--
--   The summability hypotheses are explicit because the sums are unconditional sums over an
--   arbitrary state space, which are $0$ for a non-summable family; with them the rearrangement in
--   the book's one-line proof is valid.
-- source:
--   Serfozo, Introduction to Stochastic Networks, Springer 1999, pp. 48-49 (PDF pp. 61-62), Theorem 2.5: "Suppose the Markov process X is ergodic and there exists a positive distribution pi on E and a transition function qbar on E such that qbar(x, y) = pi(x)^{-1} pi(y) q(y, x), x, y in E, (2.7) sum_y q(x, y) = sum_y qbar(x, y), x in E. (2.8) Then pi is the stationary distribution of X. Also, qbar is the transition function of a time reversal of X when X is stationary." Proof: "Under the assumptions, pi(x) sum_y q(x, y) = pi(x) sum_y qbar(x, y) = sum_y pi(y) q(y, x)." sha256 919f20ee082ec19faa80bdd923a5529fce9c4b6d3264fdb77c5efa64256bb463

import Mathlib
import Definitions.Def_SerfozoStochasticNetworks_Reversible

namespace SerfozoStochasticNetworks

theorem timeReversal_stationary {E : Type*} (q qbar : E → E → ℝ) (π : E → ℝ)
    (hπ : ∀ x, 0 < π x) (hq : ∀ x, Summable (q x)) (hqbar : ∀ x, Summable (qbar x))
    (hin : ∀ x, Summable fun y => π y * q y x)
    (hrev : ∀ x y, qbar x y = (π x)⁻¹ * π y * q y x)
    (hrate : ∀ x, ∑' y, q x y = ∑' y, qbar x y) :
    IsInvariant q π := by sorry

end SerfozoStochasticNetworks
