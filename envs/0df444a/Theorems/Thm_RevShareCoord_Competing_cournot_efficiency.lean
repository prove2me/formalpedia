-- Prove2me | Theorems.Thm_RevShareCoord_Competing_cournot_efficiency
-- name    : RevShareCoord.Competing.cournot_efficiency
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T00:53:32.465951+00:00
-- url     : https://prove2.me/theorems/e8b34272-a058-41da-bb93-3aff5f5ffaea
-- title:
--   Sec. 4.1.2 — Cournot: the efficiency at the supplier's optimal price is 1 − 1/(2 + β(n − 1))²
-- statement:
--   Let $n \ge 1$ symmetric retailers have the Cournot revenues $R_i(\bar q) = q_i(1 - q_i - \beta\sum_{j\ne i} q_j)$ with $0\le\beta<1$, and let $0<c<1$. Let $\bar q^N$ be any Nash equilibrium of the retailers' game when the supplier charges every retailer her optimal wholesale price $w^* = (1+c)/2$ (no revenue sharing), and let $\bar q^I \ge 0$ be any maximizer of the system profit $\Pi(\bar q) = \sum_i R_i(\bar q) - c\sum_i q_i$ over $\bar q \ge 0$. Then the efficiency of the channel is
--   $$\frac{\Pi(\bar q^N)}{\Pi(\bar q^I)} = 1 - \frac{1}{\big(2+\beta(n-1)\big)^2}.$$
--
--   For $\beta = 0$ the locations are independent linear markets and the efficiency is $75\%$; for $\beta > 0$ it rises quickly with the number of retailers. Competition among retailers can therefore matter more for the efficiency of a wholesale-price contract than the shape of the revenue function.
--
--   **Formalization Note** The ratio is stated for every equilibrium at $w^*$ and every system optimum, so it does not presuppose their closed forms.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 20 (PDF p. 21), Section 4.1.2, display of the efficiency

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Cournot

namespace RevShareCoord.Competing

/-- **Sec. 4.1.2, efficiency at the supplier's optimal price (p. 20).** Cournot revenues (7) with
`0 ≤ β < 1`, `n ≥ 1` symmetric retailers and unit cost `0 < c < 1`. Let `q̄^N` be any Nash
equilibrium of the retailers' game at the common wholesale price `w* = (1 + c)/2` (no revenue
sharing), and `q̄^I` any maximizer of the system profit `Π` over `q̄ ≥ 0`. Then the efficiency of
the channel is
`Π(q̄^N)/Π(q̄^I) = 1 − 1/(2 + β(n − 1))²`. -/
theorem cournot_efficiency {n : ℕ} (β c : ℝ) (hn : 1 ≤ n) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hc0 : 0 < c) (hc1 : c < 1) (qN qI : Fin n → ℝ)
    (hN : IsNashEquilibrium (cournotRevenue β) 1 (fun _ => (1 + c) / 2) qN)
    (hI0 : ∀ i, 0 ≤ qI i)
    (hI : IsMaxOn (systemProfit (cournotRevenue β) c) {q : Fin n → ℝ | ∀ i, 0 ≤ q i} qI) :
    systemProfit (cournotRevenue β) c qN / systemProfit (cournotRevenue β) c qI =
      1 - 1 / (2 + β * ((n : ℝ) - 1)) ^ 2 := by sorry

end RevShareCoord.Competing
