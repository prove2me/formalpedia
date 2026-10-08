-- Prove2me | Theorems.Thm_ServiceParts_StockLevels_expected_on_hand
-- name    : ServiceParts.StockLevels.expected_on_hand
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T07:15:33.79801+00:00
-- url     : https://prove2.me/theorems/58d3f6d7-a853-4b90-870e-746aa255ea92
-- title:
--   Section 3.4.2, p. 60 — E[On-hand] = s − λτ̄ū + B(s)
-- statement:
--   Let an item have compound Poisson demand with order rate $\lambda$, mean resupply time $\bar\tau$ and finite mean order size $\bar u$, and let $p(x) = p(x \mid \lambda\bar\tau)$ be the steady-state probability that $x$ units are on order. Under an $(s-1, s)$ policy with stock level $s$, the number on hand is $(s - x)^+$ when $x$ units are on order, and
--   $$E[\text{On-hand}] = \sum_{x \le s} (s - x)\,p(x) = s - \lambda\bar\tau\bar u + B(s),$$
--   where $B(s) = \sum_{x > s}(x - s)\,p(x)$ is the expected number of backorders.
--
--   With $\mu = \lambda\bar\tau\bar u$, the average investment in on-hand inventory of an item with unit cost $c$ is therefore $c\,[s - \mu + B(s)]$, the budget term of Problem 4.
--
--   **Formalization Note** The book obtains the identity from the constancy of the inventory position and Little's law ($E[\text{On-order}] = \lambda\bar\tau\bar u$). Here it is stated for the steady-state distribution itself, where $E[\text{On-order}] = \sum_x x\,p(x)$; the identity then contains the fact that the compound Poisson distribution has mean $\lambda\bar\tau\bar u$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 60, Section 3.4.2 (E[On-hand] = s_i − λ_i τ̄_i ū_i + B_i(s_i))

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand

namespace ServiceParts.StockLevels

theorem expected_on_hand (d : CompoundPoissonDemand) (s : ℕ) :
    d.expectedOnHand s = (s : ℝ) - d.lam * d.tbar * d.ubar + d.backorders s := by sorry

end ServiceParts.StockLevels
