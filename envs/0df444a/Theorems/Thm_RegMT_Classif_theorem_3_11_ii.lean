-- Prove2me | Theorems.Thm_RegMT_Classif_theorem_3_11_ii
-- name    : RegMT.Classif.theorem_3_11_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:05:30.707534+00:00
-- url     : https://prove2.me/theorems/113e1c50-d8a3-4003-9d79-8a935de477da
-- title:
--   Theorem 3.11(ii), p. 11 — robust classification equals program (18)
-- statement:
--   Let $N\ge1$ labeled samples $(\hat x_i,\hat y_i)$ lie in a finite-dimensional real normed feature space, with $\hat y_i\in\{-1,+1\}$. Let the label-switching cost be $d((x,y),(x',y'))=\|x-x'\|+\kappa\mathbf1_{y\ne y'}$ with $\kappa>0$, and let $\rho\ge0$. Suppose $L:\mathbb R\to[0,\infty)$ is convex and Lipschitz continuous. For each linear classifier $w$ define its robust loss as the supremum of $\mathbb E^Q[L(y\langle w,x\rangle)]$ over the Wasserstein ball of radius $\rho$ around the empirical sample distribution. Then that robust loss equals
--   $$\inf_{\lambda,s}\left\{\lambda\rho+\frac1N\sum_{i=1}^N s_i:\ L(\hat y_i\langle w,\hat x_i\rangle)\le s_i,\ L(-\hat y_i\langle w,\hat x_i\rangle)-\kappa\lambda\le s_i\ (i=1,\ldots,N),\ \operatorname{lip}(L)\|w\|_*\le\lambda\right\}.$$
--   Consequently, the infimum of the robust loss over $w$ equals the infimum of the displayed finite program over $(w,\lambda,s)$. This gives the finite convex reformulation of problem (4) asserted in Theorem 3.11(ii).
--
--   **Formalization Note** The paper says the two problems are “equivalent”; its proof gives the fixed-$w$ value identity, which also implies equal global optimal values and the same minimizing classifiers where minima exist. No attainment is claimed, including at $\rho=0$. The feature space is an abstract finite-dimensional real normed space; $w$ is a continuous linear functional and $\|w\|_*$ is its operator norm. The nonnegative loss is the standing convention of §2.1.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p. 11, Theorem 3.11(ii), (18); proof pp. 34–35

import Mathlib
import Definitions.Def_RegMT_Classif_Model

namespace RegMT.Classif

/-- Theorem 3.11(ii), p. 11: for each linear classifier the Wasserstein
worst-case loss equals program (18), and their infima over classifiers agree. -/
theorem theorem_3_11_ii {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {N : ℕ} (hN : 0 < N) (κ ρ : ℝ) (hκ : 0 < κ) (hρ : 0 ≤ ρ)
    (xhat : Fin N → V) (yhat : Fin N → Bool) (L : ℝ → ℝ)
    (hconv : ConvexOn ℝ Set.univ L)
    (hLip : ∃ K : NNReal, LipschitzWith K L)
    (hL0 : ∀ z, 0 ≤ L z) :
    (∀ w : V →L[ℝ] ℝ,
      worstCaseLoss κ ρ xhat yhat L w = value18 κ ρ xhat yhat L w) ∧
    (⨅ w : V →L[ℝ] ℝ, worstCaseLoss κ ρ xhat yhat L w) =
      (⨅ w : V →L[ℝ] ℝ, value18 κ ρ xhat yhat L w) := by sorry

end RegMT.Classif
