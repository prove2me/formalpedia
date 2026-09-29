-- Prove2me | Theorems.Thm_PathFindingLP_Centering_centrality_path_parameter
-- name    : PathFindingLP.Centering.centrality_path_parameter
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:37:45.290989+00:00
-- url     : https://prove2.me/theorems/75c2b83a-1894-4207-978d-778798f370b4
-- title:
--   Lemma 1: $\delta_{(1+\alpha)t}(\vec x,\vec w)\le(1+\alpha)\delta_t(\vec x,\vec w)+\alpha\sqrt{\|\vec w\|_1}$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ have full column rank, $b\in\mathbb R^m$, $c\in\mathbb R^n$, and let $(x,w)$ be feasible: $x\in S^0$ (so $Ax>b$) and $w\in\mathbb R^m_{>0}$. For all $\alpha\ge0$ and $t\ge0$,
--   $$\delta_{(1+\alpha)t}(x,w)\le(1+\alpha)\,\delta_t(x,w)+\alpha\sqrt{\|w\|_1},$$
--   where $\delta_t$ is the centrality of the weighted central path and $\|w\|_1=\sum_i|w_i|$.
--
--   Increasing the path parameter by a factor $1+\alpha$ worsens centrality by an amount controlled by the current centrality and the total weight. Combined with a centering step, this bounds how fast $t$ can grow while staying close to the weighted central path, which is where the $\sqrt{\|w\|_1}$ factor in the iteration count comes from.
--
--   **Formalization Note** Full column rank of $A$ is assumed (the paper leaves it implicit) so that the Hessian $A^TS_x^{-1}WS_x^{-1}A$ in the definition of $\delta_t$ is genuinely inverted.
-- source:
--   Lee, Sidford, Path Finding Methods for Linear Programming, FOCS 2014, pp. 424–433, p. 428, §IV.B, Lemma 1

import Mathlib
import Definitions.Def_PathFindingLP_Centering_WeightedCentralPath

open Matrix

namespace PathFindingLP.Centering

/-- Lemma 1 (§IV.B, p. 428): for feasible `(x, w)` and `α, t ≥ 0`,
`δ_{(1+α)t}(x, w) ≤ (1 + α) δ_t(x, w) + α √‖w‖₁`. -/
theorem centrality_path_parameter {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hA : A.rank = n) (x : Fin n → ℝ) (w : Fin m → ℝ)
    (hxw : IsFeasible A b x w) (α t : ℝ) (hα : 0 ≤ α) (ht : 0 ≤ t) :
    centrality A b c ((1 + α) * t) x w ≤
      (1 + α) * centrality A b c t x w + α * Real.sqrt (∑ i, |w i|) := by sorry

end PathFindingLP.Centering
