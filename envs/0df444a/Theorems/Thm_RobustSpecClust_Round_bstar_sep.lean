-- Prove2me | Theorems.Thm_RobustSpecClust_Round_bstar_sep
-- name    : RobustSpecClust.Round.bstar_sep
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:28.307721+00:00
-- url     : https://prove2.me/theorems/cfdfad9f-6702-4cac-9045-d8e7b9cfed28
-- title:
--   Proof of Theorem 2, p. 47 — for B* = Diag(1/√n_k)O with O orthogonal, ‖b*_l − b*_k‖ = √(1/n_k + 1/n_l)
-- statement:
--   Let $\varphi : [n]\to[r]$ be a labelling with all cluster sizes $n_k > 0$, let $O \in \mathbb R^{r\times r}$ be orthogonal and $B^* = \mathrm{Diag}(1/\sqrt{n_1},\dots,1/\sqrt{n_r})\,O$ with rows $b^*_1,\dots,b^*_r$. Then for all $k \ne l$,
--   $$\|b^*_l - b^*_k\| = \sqrt{\frac1{n_k} + \frac1{n_l}} .$$
--
--   In particular $\delta_k = 1/\sqrt{n_k}$ satisfies $\delta_k \le \min_{l \ne k}\|b^*_l - b^*_k\|$, the hypothesis of Lemma 5, so that $|\mathcal S_k|\delta_k^2 = |\mathcal S_k|/n_k$ in Theorem 2. Note $U^0 O = \Theta(\varphi)B^*$, so $V = U^0O$ is k-means feasible.
-- source:
--   arXiv:1912.07546v3, Appendix G, proof of Theorem 2, p. 47, first paragraph ("‖b*_l − b*_k‖ = √(1/n_k + 1/n_l)")

import Mathlib
import Definitions.Def_RobustSpecClust_Round_Setting

namespace RobustSpecClust.Round

open Matrix

theorem bstar_sep {n r : ℕ} (φ : Fin n → Fin r) (hφ : ∀ k, 0 < clusterSize φ k)
    (O : Matrix (Fin r) (Fin r) ℝ) (hO : O ∈ Matrix.orthogonalGroup (Fin r) ℝ)
    (k l : Fin r) (hkl : k ≠ l) :
    vecNorm ((Matrix.diagonal (fun j => 1 / Real.sqrt (clusterSize φ j)) * O) l -
        (Matrix.diagonal (fun j => 1 / Real.sqrt (clusterSize φ j)) * O) k)
      = Real.sqrt (1 / (clusterSize φ k : ℝ) + 1 / (clusterSize φ l : ℝ)) := by sorry

end RobustSpecClust.Round
