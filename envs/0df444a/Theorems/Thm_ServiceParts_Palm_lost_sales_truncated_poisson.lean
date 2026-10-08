-- Prove2me | Theorems.Thm_ServiceParts_Palm_lost_sales_truncated_poisson
-- name    : ServiceParts.Palm.lost_sales_truncated_poisson
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T22:42:11.281985+00:00
-- url     : https://prove2.me/theorems/8cd3f377-c435-4383-8988-43a4e9a1da2c
-- title:
--   Theorem 8 — lost sales with exponential resupply: the balance equations give a truncated Poisson law
-- statement:
--   Consider the lost-sales $(s-1,s)$ system with stock level $s$: orders arrive as a Poisson process with rate $\lambda > 0$, an order arriving when no stock is on hand is lost, and accepted orders have i.i.d. exponential resupply times with density $g(\tau) = \beta e^{-\beta\tau}$, $\beta > 0$, mean $\bar\tau = 1/\beta$. A vector $(\pi_0, \dots, \pi_s)$ satisfies the balance equations (3.25), (3.26), (3.32) of this system and sums to one if and only if
--   $$\pi_x = \frac{e^{-\lambda/\beta}(\lambda/\beta)^x/x!}{\sum_{n=0}^{s} e^{-\lambda/\beta}(\lambda/\beta)^n/n!} = \frac{e^{-\lambda\bar\tau}(\lambda\bar\tau)^x/x!}{\sum_{n=0}^{s} e^{-\lambda\bar\tau}(\lambda\bar\tau)^n/n!}, \qquad 0 \le x \le s.$$
--
--   So the steady-state number of units in resupply is Poisson with mean $\lambda\bar\tau$ truncated to $\{0,\dots,s\}$ (the Erlang loss distribution).
--
--   **Formalization Note** The book's "steady state probability" is the solution of the balance equations: its proof passes to $t \to \infty$ in the forward equations (3.24) assuming $P_j'(t) \to 0$, then solves (3.25)–(3.33). The statement formalizes that algebraic step, in both directions (the normalized solution exists and is unique). The sentence after the proof extending the result to arbitrary resupply densities (p. 46) is asserted without proof and is not part of this statement.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 44, Theorem 8 (proof pp. 44-46, Eqs. (3.24)-(3.34))

import Mathlib
import Definitions.Def_ServiceParts_Palm_LostSalesBalance

namespace ServiceParts.Palm

theorem lost_sales_truncated_poisson (lam β : ℝ) (hlam : 0 < lam) (hβ : 0 < β) (s : ℕ)
    (π : ℕ → ℝ) :
    (LostSalesBalance lam β s π ∧ ∑ j ∈ Finset.range (s + 1), π j = 1) ↔
      ∀ x, x ≤ s →
        π x = (Real.exp (-(lam / β)) * (lam / β) ^ x / (Nat.factorial x : ℝ)) /
          ∑ n ∈ Finset.range (s + 1),
            Real.exp (-(lam / β)) * (lam / β) ^ n / (Nat.factorial n : ℝ) := by sorry

end ServiceParts.Palm
