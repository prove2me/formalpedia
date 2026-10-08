-- Prove2me | Theorems.Thm_PariMutuel_Consensus_hasDerivAt_phi
-- name    : PariMutuel.Consensus.hasDerivAt_phi
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:22:41.03164+00:00
-- url     : https://prove2.me/theorems/118d17a6-d6f7-4fb0-a213-2ff032ebb643
-- title:
--   p. 167 — partial derivatives $\partial\varphi/\partial\xi_{ij}=b_ip_{ij}/\sum_s p_{is}\xi_{is}$
-- statement:
--   Let $P$, $b$ define a pari-mutuel market and $\varphi(\xi)=\sum_i b_i\log\sum_j p_{ij}\xi_{ij}$. At any point $\xi$ (any real $m\times n$ matrix) whose inner sums $\sum_j p_{ij}\xi_{ij}$ are all positive, the partial derivative of $\varphi$ in the variable $\xi_{ij}$ exists and equals
--
--   $$
--   \frac{\partial\varphi}{\partial\xi_{ij}}=\frac{b_i\,p_{ij}}{\sum_s p_{is}\,\xi_{is}} .
--   $$
--
--   These partial derivatives define the track probabilities (6) at a maximizer.
--
--   **Formalization Note** The partial derivative is expressed as `HasDerivAt` of the one-variable function obtained by replacing the entry $\xi_{ij}$ by $t$, at $t=\xi_{ij}$. The paper states the formula at the maximum; it holds at every point with positive inner sums, which is what is stated.
-- source:
--   Eisenberg and Gale, Consensus of subjective probabilities: the pari-mutuel method, Ann. Math. Statist. 30(1), 1959, p. 167, display after the first paragraph

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market
import Definitions.Def_PariMutuel_Consensus_Phi

namespace PariMutuel.Consensus
theorem hasDerivAt_phi {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ)
    (hξ : ∀ i, 0 < ∑ j, M.P i j * ξ i j) (i : Fin m) (j : Fin n) :
    HasDerivAt (fun t : ℝ => M.phi (Function.update ξ i (Function.update (ξ i) j t)))
      (M.b i * M.P i j / ∑ s, M.P i s * ξ i s) (ξ i j) := by sorry
end PariMutuel.Consensus
