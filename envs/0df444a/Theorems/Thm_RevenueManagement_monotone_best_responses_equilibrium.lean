-- Prove2me | Theorems.Thm_RevenueManagement_monotone_best_responses_equilibrium
-- name    : RevenueManagement.monotone_best_responses_equilibrium
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T01:03:04.200152+00:00
-- url     : https://prove2.me/theorems/e3030920-9d8c-4fe3-afec-db16ce20a97a
-- title:
--   Sect. 8.4.1.3 (Talluri): if neither firm's equilibrium graph has crossing arcs (or both are reversed), a pure-strategy equilibrium pair of arcs exists
-- statement:
--   In a two-firm game with nonempty finite chains of strategies, if the best responses of both
--   firms are monotone in the rival's strategy in the sense of the equilibrium graph, no crossing
--   arcs for both firms, or the reverse condition for both, then a pure-strategy Nash
--   equilibrium exists: following best-response arcs one either reaches an equilibrium pair or
--   doubles back and creates a crossing.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 381, Sect. 8.4.1.3 ('If the graph has no crossing arcs, as in Proposition 8.1, then there has to exist an equilibrium pair of arcs ... Thus, the game has an equilibrium'), from Talluri [503]

import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

theorem monotone_best_responses_equilibrium {m n : ℕ} (u1 u2 : Fin m → Fin n → ℝ) (hm : 0 < m)
    (hn : 0 < n) (h : (NoCrossing1 u1 ∧ NoCrossing2 u2) ∨ (ReverseCrossing1 u1 ∧ ReverseCrossing2 u2)) :
    ∃ i j, IsNashEquilibrium u1 u2 i j := by sorry

end RevenueManagement
