-- Prove2me | Theorems.Thm_RenewForward_PriceImpact_lemma_1
-- name    : RenewForward.PriceImpact.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:02.244215+00:00
-- url     : https://prove2.me/theorems/d4f5a724-69b7-4717-a456-85f010e87f85
-- title:
--   Lemma 1, p. 12 — the spot-market Cournot equilibrium given forward positions is (7), with price (8)
-- statement:
--   Fix the market parameters, a wind capacity $k_W$, forward positions $f_{P1}, f_{P2}$ of the two conventional producers, and a realization of demand $\theta$ and wind yield $\xi$. In the spot market each producer $i$ chooses $q_{Pi} \in \mathbb R$ to maximize $p_s(q_{Pi} - f_{Pi}) - c\,q_{Pi}$, where $p_s = a + \theta - \xi k_W - (q_{P1} + q_{P2})$.
--
--   Then $(q_{P1}, q_{P2})$ is a Nash equilibrium of this spot game if and only if
--   $$q_{Pi} = \frac{q_0 + 2f_{Pi} - f_{Pj}}{3}\quad(i \ne j), \qquad q_0 = a - c + \theta - \xi k_W,$$
--   and at this equilibrium the spot price is
--   $$p_s = \frac{p_0 - (f_{P1} + f_{P2})}{3}, \qquad p_0 = a + 2c + \theta - \xi k_W.$$
--
--   This is the spot stage of the model: the forward stage anticipates exactly this outcome. Selling forward raises a producer's spot output and lowers the spot price.
--
--   **Formalization Note.** The inverse demand is (6) without its $\max\{\cdot, 0\}$, as under Assumption 1. The wind producers' output $q^*_{Wi} = \xi k_{Wi}$ (they sell all available output at zero cost) is part of the model, not of this statement.
-- source:
--   Peura & Bunn, Renewable power and electricity prices: The impact of forward markets, author-accepted manuscript, LBS Research Online eprint 1432 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3710), p. 12, Lemma 1, (7)–(8)

import Mathlib
import Definitions.Def_RenewForward_PriceImpact_Setting

namespace RenewForward.PriceImpact

/-- Lemma 1 (Spot equilibrium), p. 12: given forward positions `(f1, f2)`, the spot Cournot game on the
inverse residual demand (6) (interior branch) has the unique equilibrium (7), and its price is (8). -/
theorem lemma_1 (M : Params) {Ω : Type*} (θ ξ : Ω → ℝ) (kW f1 f2 : ℝ) (w : Ω) (q1 q2 : ℝ) :
    (IsSpotEq M θ ξ kW f1 f2 w q1 q2 ↔
      q1 = spotQ M θ ξ kW f1 f2 w ∧ q2 = spotQ M θ ξ kW f2 f1 w) ∧
    (IsSpotEq M θ ξ kW f1 f2 w q1 q2 →
      spotPrice' M θ ξ kW q1 q2 w = spotP M θ ξ kW (f1 + f2) w) := by sorry

end RenewForward.PriceImpact
