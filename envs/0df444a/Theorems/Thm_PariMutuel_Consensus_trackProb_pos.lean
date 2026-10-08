-- Prove2me | Theorems.Thm_PariMutuel_Consensus_trackProb_pos
-- name    : PariMutuel.Consensus.trackProb_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:22:59.519008+00:00
-- url     : https://prove2.me/theorems/aa777da2-06c5-4d55-927e-96c47e3a7baa
-- title:
--   p. 167 — every track probability $\pi_j$ of (6) is positive
-- statement:
--   Let $\bar\xi$ maximize $\varphi$ on $D$ (with positive inner sums) for a pari-mutuel market in which every column of $P$ has a positive entry, and let $\pi_j=\max_i b_ip_{ij}/\sum_s p_{is}\bar\xi_{is}$ as in (6). Then
--
--   $$
--   \pi_j>0\qquad\text{for every } j .
--   $$
--
--   Positivity of the $\pi_j$ is what makes the ratios $p_{ij}/\pi_j$ in (3) meaningful in the existence proof.
-- source:
--   Eisenberg and Gale, Consensus of subjective probabilities: the pari-mutuel method, Ann. Math. Statist. 30(1), 1959, p. 167, proof of the EXISTENCE THEOREM, last paragraph

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market
import Definitions.Def_PariMutuel_Consensus_Phi

namespace PariMutuel.Consensus
theorem trackProb_pos {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ)
    (hξ : M.IsPhiMaximizer ξ) (j : Fin n) : 0 < M.trackProb ξ j := by sorry
end PariMutuel.Consensus
