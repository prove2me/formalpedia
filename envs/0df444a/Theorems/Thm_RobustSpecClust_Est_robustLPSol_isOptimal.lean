-- Prove2me | Theorems.Thm_RobustSpecClust_Est_robustLPSol_isOptimal
-- name    : RobustSpecClust.Est.robustLPSol_isOptimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:25.314994+00:00
-- url     : https://prove2.me/theorems/c79cc73c-c2cd-4dc3-a5d7-0391fa3c6a5d
-- title:
--   §3, p. 10 — the closed form X̂_ij = 1{K_ij − γ > 0} solves Robust-LP
-- statement:
--   Let $\iota$ be a finite index set, $K \in \mathbb R^{\iota\times\iota}$ and $\gamma \in \mathbb R$. Let $\hat X$ be the matrix with $\hat X_{ij} = 1$ if $K_{ij} - \gamma > 0$ and $\hat X_{ij} = 0$ otherwise. Then $\hat X \in [0,1]^{\iota\times\iota}$, and for every $X$ with $0 \le X_{ij} \le 1$ for all $i, j$,
--   $$\langle K - \gamma E, X\rangle \le \langle K - \gamma E, \hat X\rangle ,$$
--   where $E$ is the all-ones matrix and $\langle A, B\rangle = \sum_{ij} A_{ij}B_{ij}$.
--
--   So $\hat X$ is an optimal solution of the Robust-LP $\max\{\langle K - \gamma E_N, X\rangle : 0 \le X_{ij} \le 1\}$. This identifies the algorithm's output with an explicit thresholding of the kernel, which is the form analysed in Theorem 1.
-- source:
--   arXiv:1912.07546v3, §3, p. 9 (Robust-LP) and p. 10 (closed form of X̂)

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory

namespace RobustSpecClust.Est

theorem robustLPSol_isOptimal {ι : Type*} [Fintype ι] (K : Matrix ι ι ℝ) (γ : ℝ) :
    (∀ i j, 0 ≤ robustLPSol K γ i j ∧ robustLPSol K γ i j ≤ 1) ∧
    ∀ X : Matrix ι ι ℝ, (∀ i j, 0 ≤ X i j ∧ X i j ≤ 1) →
      frobInner (K - γ • ones ι) X ≤ frobInner (K - γ • ones ι) (robustLPSol K γ) := by sorry

end RobustSpecClust.Est
