-- Prove2me | Theorems.Thm_PostTradeFees_Welfare_corollary_3
-- name    : PostTradeFees.Welfare.corollary_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:22.954669+00:00
-- url     : https://prove2.me/theorems/5d0138a6-4db4-4221-bb8f-71ead5a58d7c
-- title:
--   Corollary 3, p. 16 (PDF 17) — neither fee structure maximizes welfare at every cost
-- statement:
--   Let $N>1$, $V_h>V_l\ge0$, and $c>0$. Compare the stationary welfare of the "all" and "own" trading chains, and the welfare realized by a stationary equilibrium under each fee structure. With
--
--   $$
--   c_1=\frac{2N(N-1)(V_h-V_l)}{(2N+1)(2N-1)},\qquad
--   c_2=\frac{N(V_h-V_l)}{2N+1},
--   $$
--
--   three regimes occur:
--
--   1. If $c\le c_1$, "all" has strictly greater welfare and both fee structures induce it.
--   2. If $c_1<c\le c_2$, "all" has at least as much welfare; uniform fees induce "all" while trade-specific fees induce "own".
--   3. If $c>c_2$, "own" has strictly greater welfare; trade-specific fees induce it and realize strictly greater welfare than uniform fees.
--
--   Thus neither fee structure realizes the socially preferred trading pattern at every cost.
--
--   **Formalization Note** The theorem quantifies over equilibria and stationary distributions; the existence results are separate milestones. At $c=c_2$, the two welfare values tie, so both realized welfare levels attain the same maximum even though the paper's prose says "only" uniform fees achieve it. The statements retain the paper's strict and weak comparisons and the different strategies.
-- source:
--   Degryse, Van Achter & Wuyts, Plumbing of Securities Markets, SSRN 2023597 (version of October 2016), p. 16 (PDF 17), Corollary 3

import Mathlib
import Definitions.Def_PostTradeFees_Welfare_Model

namespace PostTradeFees.Welfare

/-- Corollary 3, three cost ranges and the welfare realized by each fee structure. -/
theorem corollary_3 (P : Params) (hS : P.Standing)
    (φa φo : Fin 3 → ℝ)
    (hφa : MarkovChain.IsStationary (chainAll P.N) φa)
    (hφo : MarkovChain.IsStationary (chainOwn P.N) φo)
    (VbU VsU VbT VsT : ℝ)
    (hU : IsEquilibrium P .uniform VbU VsU)
    (hT : IsEquilibrium P .tradeSpecific VbT VsT)
    (φU φT : Fin 3 → ℝ)
    (hφU : MarkovChain.IsStationary (eqChain P .uniform VbU VsU) φU)
    (hφT : MarkovChain.IsStationary (eqChain P .tradeSpecific VbT VsT) φT) :
    (P.c ≤ c1 P →
      welfare P φo < welfare P φa ∧
      PlaysAll P .uniform VbU VsU ∧ PlaysAll P .tradeSpecific VbT VsT ∧
      welfare P φU = welfare P φa ∧ welfare P φT = welfare P φa) ∧
    (c1 P < P.c → P.c ≤ c2 P →
      welfare P φo ≤ welfare P φa ∧
      PlaysAll P .uniform VbU VsU ∧ PlaysOwn P .tradeSpecific VbT VsT ∧
      welfare P φU = welfare P φa ∧ welfare P φT = welfare P φo) ∧
    (c2 P < P.c →
      welfare P φa < welfare P φo ∧
      PlaysOwn P .tradeSpecific VbT VsT ∧ ¬ PlaysOwn P .uniform VbU VsU ∧
      welfare P φT = welfare P φo ∧ welfare P φU < welfare P φT) := by sorry

end PostTradeFees.Welfare
