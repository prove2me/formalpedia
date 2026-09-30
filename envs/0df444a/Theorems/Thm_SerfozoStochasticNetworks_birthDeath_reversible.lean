-- Prove2me | Theorems.Thm_SerfozoStochasticNetworks_birthDeath_reversible
-- name    : SerfozoStochasticNetworks.birthDeath_reversible
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-19T02:50:47.328999+00:00
-- url     : https://prove2.me/theorems/8c9081f6-7f60-478b-b026-3607e3dd8641
-- title:
--   Example 2.1 — the birth-death process is reversible
-- statement:
--   Consider the classical birth–death process on the non-negative integers: from state $x$ the
--   arrival rate is $\lambda(x)>0$ and the departure rate is $\mu(x)>0$ for $x\ge1$, all other rates
--   being zero. Let
--   $$\pi(x)=\prod_{n=1}^{x}\frac{\lambda(n-1)}{\mu(n)},\qquad \pi(0)=1 .$$
--
--   Then $\pi$ satisfies the detailed balance equations for these rates, and consequently the rate
--   function is reversible.
--
--   The single family of equations $\pi(x)\lambda(x)=\pi(x+1)\mu(x+1)$ carries everything: the
--   equations for $y=x+1$ and for $y=x-1$ are the same family read from the two ends, and a
--   backward iteration solves them.
--
--   **Formalization Note** The rates are given as an explicit function: $q(x,y)=\lambda(x)$ when
--   $y=x+1$, $q(x,y)=\mu(x)$ when $x=y+1$, and $0$ otherwise, so in particular $q(x,x)=0$ and
--   $q(x,y)=0$ whenever $|x-y|\ge2$. The value $\mu(0)$ never appears, the state $-1$ not existing,
--   which is why only $\mu(n+1)$ is assumed positive.
--
--   $\pi$ is normalized at the origin rather than carrying the free constant $\pi(0)$ of the book;
--   detailed balance is homogeneous, so this is no loss. Nothing is claimed about summability of
--   $\pi$: whether the process has a stationary *distribution* depends on the convergence of
--   $\sum_x\pi(x)$, which the book records separately and which is not part of this statement.
-- source:
--   Serfozo, Introduction to Stochastic Networks, Springer 1999, pp. 45-46 (PDF pp. 58-59), Example 2.1: "Birth-Death Process. ... Its detailed balance equations for y = x + 1 and y = x - 1 are respectively pi(x) lambda(x) = pi(x + 1) mu(x + 1), x >= 0, pi(x) mu(x) = pi(x - 1) lambda(x - 1), x >= 1. But these two equations are the same. The second one yields pi(x) = pi(x - 1) lambda(x - 1)/mu(x), x >= 1. By a backward iteration of this equation, it follows that it has a solution pi(x) = pi(0) prod_{n=1}^{x} lambda(n - 1)/mu(n), x >= 1. (2.3) Thus, the process is reversible with invariant measure pi." sha256 919f20ee082ec19faa80bdd923a5529fce9c4b6d3264fdb77c5efa64256bb463

import Mathlib
import Definitions.Def_SerfozoStochasticNetworks_Reversible

namespace SerfozoStochasticNetworks

theorem birthDeath_reversible (lam mu : ℕ → ℝ) (hlam : ∀ n, 0 < lam n)
    (hmu : ∀ n, 0 < mu (n + 1)) :
    DetailedBalance (birthDeathRate lam mu) (birthDeathMeasure lam mu) ∧
      IsReversible (birthDeathRate lam mu) := by sorry

end SerfozoStochasticNetworks
