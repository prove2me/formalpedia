-- Prove2me | Theorems.Thm_PariMutuel_Consensus_uniqueness_theorem
-- name    : PariMutuel.Consensus.uniqueness_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:03:44.099985+00:00
-- url     : https://prove2.me/theorems/3263fc31-895d-4628-8dd1-37fdb09c0549
-- title:
--   UNIQUENESS THEOREM — equilibrium probabilities are unique
-- statement:
--   Let $P$, $b$ define a pari-mutuel market. If $(\pi,\beta)$ and $(\bar\pi,\bar\beta)$ are two pairs of equilibrium probabilities and bets (nonnegative numbers satisfying (1), (2) and (3)), then
--
--   $$
--   \pi_j=\bar\pi_j\qquad\text{for every } j .
--   $$
--
--   The bets need not coincide; only the track probabilities are determined by the market, which is what makes the pari-mutuel consensus well defined.
--
--   **Formalization Note** The statement ranges over all equilibria, not only those constructed from a maximizer of $\varphi$. Condition (3) is multiplied out (see `Market`).
-- source:
--   Eisenberg and Gale, Consensus of subjective probabilities: the pari-mutuel method, Ann. Math. Statist. 30(1), 1959, p. 168, UNIQUENESS THEOREM

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market

namespace PariMutuel.Consensus
theorem uniqueness_theorem {m n : ℕ} (M : Market m n) (π π' : Fin n → ℝ)
    (β β' : Fin m → Fin n → ℝ) (h : M.IsEquilibrium π β) (h' : M.IsEquilibrium π' β') :
    π = π' := by sorry
end PariMutuel.Consensus
