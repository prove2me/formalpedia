-- Prove2me | Theorems.Thm_TradingFavors_Existence_proposition_1
-- name    : TradingFavors.Existence.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:15.244635+00:00
-- url     : https://prove2.me/theorems/d0cc4c9d-0b78-4c93-990e-8920777f8774
-- title:
--   Proposition 1, p. 13 (PDF 13) — the no-collaboration profile σᴺᶜ is always a TFE
-- statement:
--   Under the standing assumptions, the no-collaboration profile $\sigma^{NC}$, with $\sigma^{NC}_1(k)=\sigma^{NC}_2(k)=1$ for all $k\in\mathbb Z$, is a trading-favors equilibrium: condition (4) holds for both firms at every $k\in\mathbb Z$.
--
--   So a TFE always exists; the question of the mission is when a non-trivial one does.
--
--   **Formalization Note** Here TFE is Definition 1 literally, condition (4) at every integer $k$.
-- source:
--   Hu & Caldentey, Trust and Reciprocity in Firms’ Capacity Sharing, SSRN 4348127 (version of February 6, 2023), p. 13 (PDF 13), Proposition 1; proof p. A3 (PDF 33)

import Mathlib
import Definitions.Def_TradingFavors_Existence_Model

namespace TradingFavors.Existence

theorem proposition_1 (θ : Params) (hθ : θ.Standing) : IsTFE θ sigmaNC := by sorry

end TradingFavors.Existence
