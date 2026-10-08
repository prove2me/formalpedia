-- Prove2me | Theorems.Thm_PariMutuel_Consensus_existence_theorem
-- name    : PariMutuel.Consensus.existence_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:23:02.173997+00:00
-- url     : https://prove2.me/theorems/11d93b83-a7b7-4a7a-b5c1-1737e906af08
-- title:
--   EXISTENCE THEOREM — (6)–(7) at a maximizer of $\varphi$ are equilibrium probabilities and bets
-- statement:
--   Let $P$, $b$ define a pari-mutuel market, and let $\bar\xi$ be any maximizer of $\varphi(\xi)=\sum_i b_i\log\sum_j p_{ij}\xi_{ij}$ on $D$ (with positive inner sums). Define
--
--   $$
--   \text{(6)}\ \pi_j=\max_i\frac{b_i\,p_{ij}}{\sum_s p_{is}\bar\xi_{is}},\qquad \text{(7)}\ \beta_{ij}=\bar\xi_{ij}\,\pi_j .
--   $$
--
--   Then $\pi_j$ and $\beta_{ij}$ are equilibrium probabilities and bets: they are nonnegative and satisfy (1) the budget relation, (2) the pari-mutuel condition and (3) the optimality of each bettor's strategy.
--
--   Together with the existence of a maximizer, this proves that equilibria exist, and it does so constructively from a concave program.
--
--   **Formalization Note** The conclusion is `IsEquilibrium`, in which (3) is written multiplied out (see the definition `Market`). The statement holds for every maximizer, not just for some.
-- source:
--   Eisenberg and Gale, Consensus of subjective probabilities: the pari-mutuel method, Ann. Math. Statist. 30(1), 1959, p. 167, EXISTENCE THEOREM, (6)–(7)

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market
import Definitions.Def_PariMutuel_Consensus_Phi

namespace PariMutuel.Consensus
theorem existence_theorem {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ)
    (hξ : M.IsPhiMaximizer ξ) : M.IsEquilibrium (M.trackProb ξ) (M.bets ξ) := by sorry
end PariMutuel.Consensus
