-- Prove2me | Theorems.Thm_PariMutuel_Consensus_cauchy_schwarz_step
-- name    : PariMutuel.Consensus.cauchy_schwarz_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:45:58.649794+00:00
-- url     : https://prove2.me/theorems/2da2a6f3-cc9c-46d2-acc8-019dfd767f5e
-- title:
--   p. 168 — Cauchy–Schwarz step: $\sum_k\bar\pi_k^2/\pi_k\le1$ forces $\bar\pi=\pi$
-- statement:
--   Let $\pi=(\pi_1,\dots,\pi_n)$ and $\bar\pi=(\bar\pi_1,\dots,\bar\pi_n)$ be real vectors with $\pi_k>0$ and $\bar\pi_k\ge 0$ for all $k$, and $\sum_k\pi_k=\sum_k\bar\pi_k=1$. If
--
--   $$
--   \sum_{k=1}^n\frac{\bar\pi_k\,\bar\pi_k}{\pi_k}\le 1,
--   $$
--
--   then $\bar\pi_k=\pi_k$ for every $k$.
--
--   In the paper this is the equality case of the Cauchy–Schwarz inequality for $x_k=\bar\pi_k/\sqrt{\pi_k}$, $y_k=\sqrt{\pi_k}$, and it closes the proof of the UNIQUENESS THEOREM.
--
--   **Formalization Note** The page has $\bar\pi_k>0$ (equilibrium probabilities are positive); only $\bar\pi_k\ge 0$ is assumed here, which gives a formally stronger lemma. $\bar\pi$ is written `π'`.
-- source:
--   Eisenberg and Gale, Consensus of subjective probabilities: the pari-mutuel method, Ann. Math. Statist. 30(1), 1959, p. 168, proof of the UNIQUENESS THEOREM, Cauchy–Schwarz display

import Mathlib

namespace PariMutuel.Consensus
theorem cauchy_schwarz_step {n : ℕ} (π π' : Fin n → ℝ) (hπ : ∀ k, 0 < π k)
    (hπ' : ∀ k, 0 ≤ π' k) (hs : ∑ k, π k = 1) (hs' : ∑ k, π' k = 1)
    (h : ∑ k, π' k * π' k / π k ≤ 1) : π' = π := by sorry
end PariMutuel.Consensus
