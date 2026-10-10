-- Prove2me | Theorems.Thm_PriceQualityService_Oligopoly_eq_EC_1
-- name    : PriceQualityService.Oligopoly.eq_EC_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:00.576984+00:00
-- url     : https://prove2.me/theorems/75a8e20e-7871-4c4c-b979-27b3ad948ef6
-- title:
--   (EC.1): a firm's MNL profit is the unique root of a monotone equation
-- statement:
--   Fix prices $\mathbf p$, qualities $\mathbf q$ and durations $\mathbf t$, and a firm $i$. A real number $r_i$ equals firm $i$'s profit $\Pi_i(\mathbf p, \mathbf q, \mathbf t; \mathcal N)$ if and only if
--   $$
--   r_i \Big(1 + \sum_{j \ne i} \exp(\alpha_j q_j - p_j + t_j s_j)\Big) = \big[p_i - c_i q_i^2 - t_i(a_i - b_i q_i) - r_i\big] \exp(\alpha_i q_i - p_i + t_i s_i).
--   $$
--   In particular this equation has exactly one root $r_i$, the profit.
--
--   This turns firm $i$'s best-response problem into maximizing the root of an equation whose left side increases and whose right side decreases in $r_i$.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 2 (PDF p. 35), (EC.1)

import Mathlib
import Definitions.Def_PriceQualityService_Oligopoly_Model

namespace PriceQualityService.Oligopoly

open Finset

/-- (EC.1), Online Supplement p. 2: for given strategies of the other firms, a real `r` is firm
`i`'s profit (6) if and only if
`r (1 + ∑_{j ≠ i} exp(α_j q_j − p_j + t_j s_j)) = [p_i − c_i q_i² − t_i(a_i − b_i q_i) − r] ·
exp(α_i q_i − p_i + t_i s_i)`; in particular this equation has exactly one root in `r`. -/
theorem eq_EC_1 {N : ℕ} (α a b c s p q t : Fin N → ℝ) (i : Fin N) (r : ℝ) :
    r * (1 + ∑ j ∈ univ.erase i, PriceQualityService.Joint.attraction α s p q t j) =
        (PriceQualityService.Joint.markup a b c p q t i - r) * PriceQualityService.Joint.attraction α s p q t i ↔
      r = firmProfit α a b c s p q t i := by sorry

end PriceQualityService.Oligopoly
