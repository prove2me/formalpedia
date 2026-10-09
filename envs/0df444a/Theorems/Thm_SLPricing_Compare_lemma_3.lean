-- Prove2me | Theorems.Thm_SLPricing_Compare_lemma_3
-- name    : SLPricing.Compare.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:32.074318+00:00
-- url     : https://prove2.me/theorems/837ae4e6-fb4a-48dc-89aa-ec8cbebe3136
-- title:
--   Lemma 3, p. 20 — under responsive pricing the second-period price (6) is optimal for every $q_u$ and $\bar x$
-- statement:
--   Consider responsive pricing in the mission's model. Suppose the first-period buyers are the types $[\bar x, 1]$ for some $\bar x \in [0,1]$, so that the types $[0,\bar x)$ remain. Given the realized posterior mean $q_u$, the firm's second-period profit at price $p_2$ is
--   $$\pi_2(p_2) = (p_2 - c)\,\big|\{x \in [0,\bar x) : x + q_u \ge p_2\}\big| = (p_2-c)\,\big[\min(\bar x,\ \bar x + q_u - p_2)\big]^+ .$$
--   Let $p_2^*(q_u,\bar x)$ be the price (6). Then:
--   1. $p_2^*(q_u,\bar x)$ maximizes $\pi_2$ over all $p_2 \in \mathbb R$;
--   2. if $\bar x > 0$ and $q_u > c - \bar x$, it is the unique maximizer;
--   3. if $q_u \le c - \bar x$, every maximizer sells nothing in period 2 (the firm exits).
--
--   Part (ii) of the paper's lemma (the second-period buyers are the types $x_i \ge p_2^* - q_u$ among those remaining) is built into the profit function. The lemma pins down the subgame that follows any first-period outcome and is the input for computing the responsive profit.
--
--   **Formalization Note** The paper says "unique equilibrium" for all $q_u$, $\bar x$. Literally, uniqueness holds only for $q_u > c - \bar x$ and $\bar x > 0$: in the exit region every price at or above $c$ that sells nothing is optimal, and (6)'s choice $p_2^* = c$ is the paper's convention (p. 20); for $\bar x = 0$ no consumer remains and every price is optimal. Part 3 states what is unique in the exit region, namely the outcome.
-- source:
--   Papanastasiou–Savva, accepted manuscript MS-14-00028.R2 (2016), Lemma 3, p. 20

import Mathlib
import Definitions.Def_SLPricing_Compare_Model
import Definitions.Def_SLPricing_Resp_P2Star
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SLPricing.Compare

/-- Lemma 3, p. 20: when the types `[x̄, 1]` bought in period 1, the price `p2Star c q_u x̄` of (6)
maximizes the firm's second-period profit at every realization `q_u`; it is the unique maximizer
when `q_u > c − x̄` (and `x̄ > 0`), and when `q_u ≤ c − x̄` every maximizer sells nothing. -/
theorem lemma_3 (P : Params) (hP : P.Standing) (B : Set ℝ) (xbar : ℝ)
    (hx : xbar ∈ Icc (0 : ℝ) 1) (hB : B = Icc xbar 1) (q : ℝ) :
    (∀ p₂, secondProfit P B q p₂ ≤ secondProfit P B q (SLPricing.Resp.p2Star P.c q xbar)) ∧
    (0 < xbar → P.c - xbar < q → ∀ p₂, (∀ p, secondProfit P B q p ≤ secondProfit P B q p₂) →
      p₂ = SLPricing.Resp.p2Star P.c q xbar) ∧
    (q ≤ P.c - xbar → ∀ p₂, (∀ p, secondProfit P B q p ≤ secondProfit P B q p₂) →
      lateMass B p₂ q = 0) := by sorry

end SLPricing.Compare
