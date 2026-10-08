-- Prove2me | Theorems.Thm_PariMutuel_Consensus_equilibrium_prob_pos
-- name    : PariMutuel.Consensus.equilibrium_prob_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:03:33.822987+00:00
-- url     : https://prove2.me/theorems/593185ab-ce39-4ad6-97ca-b8464c04dcea
-- title:
--   p. 168 — equilibrium probabilities are positive
-- statement:
--   Let $P$, $b$ define a pari-mutuel market (every column of $P$ has a positive entry, $b_i>0$), and let $\pi_j$, $\beta_{ij}$ be any equilibrium probabilities and bets, i.e. nonnegative numbers satisfying (1), (2) and (3). Then
--
--   $$
--   \pi_j>0\qquad\text{for every } j .
--   $$
--
--   The proof of the UNIQUENESS THEOREM uses that the $\pi_j$ (and hence $\mu_i=\max_s p_{is}/\pi_s$) are positive at any equilibrium; the paper asserts this without proof.
--
--   **Formalization Note** Positivity is not part of the definition of equilibrium; it is derived here from the multiplied-out condition (3), the no-zero-column assumption and $b_i>0$.
-- source:
--   Eisenberg and Gale, Consensus of subjective probabilities: the pari-mutuel method, Ann. Math. Statist. 30(1), 1959, p. 168, proof of the UNIQUENESS THEOREM ("since μ_i, μ̄_i, π_j, π_k are positive")

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market

namespace PariMutuel.Consensus
theorem equilibrium_prob_pos {m n : ℕ} (M : Market m n) (π : Fin n → ℝ) (β : Fin m → Fin n → ℝ)
    (h : M.IsEquilibrium π β) (j : Fin n) : 0 < π j := by sorry
end PariMutuel.Consensus
