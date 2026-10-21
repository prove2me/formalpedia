-- Prove2me | Theorems.Thm_PropVolSampling_Reduction_relaxation_ratio
-- name    : PropVolSampling.Reduction.relaxation_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:32.689688+00:00
-- url     : https://prove2.me/theorems/1bc0688e-a7c2-44cc-93d8-fe53e94da2ec
-- title:
--   Proof of Theorem 1.3, p. 9 — $\operatorname{tr}(V(x)V(x)^\top)^{-1}$ as a ratio of $x$-weighted Cauchy–Binet sums
-- statement:
--   Let $d\ge 1$, $V=[v_1,\dots,v_n]$ a real $d\times n$ matrix and $x\in\mathbb R^n$ with $x\ge 0$ such that $V(x)V(x)^\top=\sum_i x_iv_iv_i^\top$ is positive definite. Then
--   $$\operatorname{tr}\big(V(x)V(x)^\top\big)^{-1}=\frac{\sum_{|T|=d-1,\,T\subseteq[n]}\det(V_T^\top V_T)\,x^T}{\sum_{|R|=d,\,R\subseteq[n]}\det(V_R^\top V_R)\,x^R}.$$
--
--   This is the right-hand side of (7): the relaxation's objective at $x$ in the same Cauchy–Binet form as the expected objective of proportional volume sampling.
--
--   **Formalization Note** Positive definiteness of $\sum_ix_iv_iv_i^\top$ is assumed: otherwise the page's objective is $+\infty$ while Lean's inverse is the junk $0$. $x\ge0$ is the page's $x\in\mathbb R^n_+$; $1\le d$ is added because $d-1$ is natural-number subtraction.
-- source:
--   Nikolov, Singh, Tantipongpipat, Proportional Volume Sampling and Approximation Algorithms for A-Optimal Design, arXiv:1802.08318v5, p. 9, proof of Theorem 1.3, third display

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model

namespace PropVolSampling.Reduction
open Matrix Finset

theorem relaxation_ratio {d n : ℕ} (hd : 1 ≤ d) (V : Matrix (Fin d) (Fin n) ℝ) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hpd : (weightedGram V x).PosDef) :
    aObj (weightedGram V x) =
      (∑ T ∈ powersetCard (d - 1) (univ : Finset (Fin n)),
          ((colSub V T)ᵀ * colSub V T).det * xPow x T) /
        (∑ R ∈ powersetCard d (univ : Finset (Fin n)),
          ((colSub V R)ᵀ * colSub V R).det * xPow x R) := by sorry

end PropVolSampling.Reduction
