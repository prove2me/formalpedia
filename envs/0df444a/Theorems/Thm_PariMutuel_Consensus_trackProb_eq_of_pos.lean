-- Prove2me | Theorems.Thm_PariMutuel_Consensus_trackProb_eq_of_pos
-- name    : PariMutuel.Consensus.trackProb_eq_of_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:22:44.51923+00:00
-- url     : https://prove2.me/theorems/c9a099e9-2b94-4e72-acb3-b569585d2bd4
-- title:
--   (8) — if $\bar\xi_{ij}>0$ then $\pi_j=\partial\varphi/\partial\bar\xi_{ij}$
-- statement:
--   Let $\bar\xi$ maximize $\varphi(\xi)=\sum_i b_i\log\sum_j p_{ij}\xi_{ij}$ on $D$ (with positive inner sums), and let $\pi_j=\max_i b_ip_{ij}/\sum_s p_{is}\bar\xi_{is}$ as in (6). Then for all $i,j$,
--
--   $$
--   \bar\xi_{ij}>0\ \Longrightarrow\ \pi_j=\frac{b_i\,p_{ij}}{\sum_s p_{is}\,\bar\xi_{is}}=\frac{\partial\varphi}{\partial\bar\xi_{ij}} .
--   $$
--
--   This is the first-order optimality condition behind the verification of (1) and (3) in the EXISTENCE THEOREM.
-- source:
--   Eisenberg and Gale, Consensus of subjective probabilities: the pari-mutuel method, Ann. Math. Statist. 30(1), 1959, p. 167, (8), proof of the EXISTENCE THEOREM

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market
import Definitions.Def_PariMutuel_Consensus_Phi

namespace PariMutuel.Consensus
theorem trackProb_eq_of_pos {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ)
    (hξ : M.IsPhiMaximizer ξ) (i : Fin m) (j : Fin n) (hij : 0 < ξ i j) :
    M.trackProb ξ j = M.b i * M.P i j / ∑ s, M.P i s * ξ i s := by sorry
end PariMutuel.Consensus
