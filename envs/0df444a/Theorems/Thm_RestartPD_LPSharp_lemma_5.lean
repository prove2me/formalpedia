-- Prove2me | Theorems.Thm_RestartPD_LPSharp_lemma_5
-- name    : RestartPD.LPSharp.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:17.740616+00:00
-- url     : https://prove2.me/theorems/3e32bab6-cfe1-416d-8202-0f62568aca47
-- title:
--   Lemma 5, p. 15 — the LP primal-dual problem (19) is 1/(H(K)√(1+4R²))-sharp on W_R(0)
-- statement:
--   **Sharpness of linear programming.** Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, $c\in\mathbb R^n$ and consider the primal-dual problem (19), $\min_{x\ge0}\max_{y}\ c^\top x+y^\top b-y^\top Ax$, on $Z=\{x\ge0\}\times\mathbb R^m$ with the Euclidean norm on $\mathbb R^{n+m}$. Assume (19) has a solution, i.e. its saddle-point set $Z^\star$ is nonempty. Let $H(K)>0$ be a Hoffman constant of the KKT system (20) in the Euclidean norm, i.e. a constant with
--   $$\operatorname{dist}(z,Z^\star)\le H(K)\,\|(h-Kz)^+\| \quad\text{for all } z\in\mathbb R^{n+m}. \qquad (26)$$
--   Then for every $R\in(0,\infty)$ the problem (19) is $\alpha$-sharp on $W_R(0)=\{z\in Z:\|z\|\le R\}$ with
--   $$\alpha=\frac{1}{H(K)\sqrt{1+4R^2}},$$
--   that is, $\alpha\,\operatorname{dist}(z,Z^\star)\le\rho_r(z)$ for every $z\in W_R(0)$ and every $r\in(0,\operatorname{diam}(W_R(0))]$.
--
--   This is the paper's first contribution: it supplies the sharpness hypothesis of its restart theorems for LP, which yields linear convergence of restarted PDHG, extragradient and ADMM on linear programs.
--
--   **Formalization Note** $H(K)$ enters through its defining property (26), quantified over all $z\in\mathbb R^{n+m}$ (not only $z\in Z$); the result is stated for any constant with that property, which includes the Hoffman constant. $H>0$ is assumed (a Hoffman constant is positive). Sharpness is Definition 1, with $r$ ranging over $(0,\operatorname{diam}(W_R(0))]$ and the diameter computed in the extended reals.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, p. 15, Lemma 5 (with (26), p. 14)

import Mathlib
import Definitions.Def_RestartPD_LPSharp_PrimalDual
import Definitions.Def_RestartPD_LPSharp_LP
open scoped InnerProductSpace Matrix

namespace RestartPD.LPSharp

theorem lemma_5 {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (hsol : (Zstar (lpL A b c) lpX Set.univ).Nonempty)
    (H : ℝ) (hHpos : 0 < H)
    (hH : ∀ z : PDSpace n m, distZ (lpL A b c) lpX Set.univ z ≤ H * kktRes A b c z)
    (R : ℝ) (hR : 0 < R) :
    IsSharpOn (lpL A b c) lpX Set.univ (1 / (H * Real.sqrt (1 + 4 * R ^ 2)))
      (Wball lpX Set.univ R 0) := by sorry

end RestartPD.LPSharp
