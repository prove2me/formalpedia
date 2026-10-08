-- Prove2me | Theorems.Thm_PariMutuel_Consensus_sum_sq_div_le_one
-- name    : PariMutuel.Consensus.sum_sq_div_le_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:03:32.593622+00:00
-- url     : https://prove2.me/theorems/9d8f137e-7f1b-4207-bfee-9bdcffaf5bf1
-- title:
--   p. 168 — $\sum_k \bar\pi_k\bar\pi_k/\pi_k\le 1$ for two equilibria
-- statement:
--   Let $P$, $b$ define a pari-mutuel market, and let $(\pi,\beta)$ and $(\bar\pi,\bar\beta)$ be two pairs of equilibrium probabilities and bets. Then
--
--   $$
--   \sum_{k=1}^n \frac{\bar\pi_k\,\bar\pi_k}{\pi_k}\le 1 .
--   $$
--
--   This is the key inequality of the uniqueness proof; it is obtained from the per-bettor inequalities $\beta_{ij}\mu_i\pi_j=\beta_{ij}p_{ij}\le\beta_{ij}\bar\mu_i\bar\pi_j$ and $\bar\beta_{ik}\bar\mu_i\bar\pi_k=\bar\beta_{ik}p_{ik}\le\bar\beta_{ik}\mu_i\pi_k$ stated on the page.
--
--   **Formalization Note** $\bar\pi$ is written `π'`. Every $\pi_k$ is positive at an equilibrium, so the quotients are genuine.
-- source:
--   Eisenberg and Gale, Consensus of subjective probabilities: the pari-mutuel method, Ann. Math. Statist. 30(1), 1959, p. 168, proof of the UNIQUENESS THEOREM, first paragraph

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market

namespace PariMutuel.Consensus
theorem sum_sq_div_le_one {m n : ℕ} (M : Market m n) (π π' : Fin n → ℝ)
    (β β' : Fin m → Fin n → ℝ) (h : M.IsEquilibrium π β) (h' : M.IsEquilibrium π' β') :
    ∑ k, π' k * π' k / π k ≤ 1 := by sorry
end PariMutuel.Consensus
