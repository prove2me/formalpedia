-- Prove2me | Theorems.Thm_RWPI_Classif_theorem_2
-- name    : RWPI.Classif.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:53:46.571758+00:00
-- url     : https://prove2.me/theorems/709db8b0-97af-4e95-9bff-0fa338b06bab
-- title:
--   Theorem 2 — ℓp-regularized logistic regression and the hinge-loss SVM are Wasserstein DRO under the label-preserving cost N_q
-- statement:
--   Let $(X_1,Y_1),\dots,(X_n,Y_n)$ be training data with $X_i \in \mathbb R^d$, labels $Y_i \in \{-1,+1\}$ and $n \ge 1$, and let $P_n$ be their empirical distribution. Let $q \in [1,\infty]$ and let $p$ be its conjugate exponent, $1/p + 1/q = 1$. Let $D_c$ be the optimal transport cost with the label-preserving cost
--
--   $$c\big((x,y),(u,v)\big) = N_q\big((x,y),(u,v)\big) = \begin{cases}\|x-u\|_q & y = v,\\ +\infty & y \ne v,\end{cases}$$
--
--   (exponent $\rho = 1$), and let $\delta \ge 0$. Then for every $\beta \in \mathbb R^d$:
--
--   1. (logistic regression)
--   $$\sup_{P:\ D_c(P,P_n)\le\delta} \mathbb E_P\Big[\log\big(1 + e^{-Y\beta^T X}\big)\Big] = \frac1n\sum_{i=1}^n \log\big(1 + e^{-Y_i\beta^T X_i}\big) + \delta\,\|\beta\|_p ;$$
--   2. (support vector machine)
--   $$\sup_{P:\ D_c(P,P_n)\le\delta} \mathbb E_P\Big[\big(1 - Y\beta^T X\big)^+\Big] = \frac1n\sum_{i=1}^n \big(1 - Y_i\beta^T X_i\big)^+ + \delta\,\|\beta\|_p .$$
--
--   Consequently,
--
--   $$\inf_{\beta\in\mathbb R^d}\ \sup_{P:\ D_c(P,P_n)\le\delta} \mathbb E_P\Big[\log\big(1 + e^{-Y\beta^T X}\big)\Big] = \inf_{\beta\in\mathbb R^d}\Big\{\frac1n\sum_{i=1}^n \log\big(1 + e^{-Y_i\beta^T X_i}\big) + \delta\,\|\beta\|_p\Big\},$$
--
--   $$\inf_{\beta\in\mathbb R^d}\ \sup_{P:\ D_c(P,P_n)\le\delta} \mathbb E_P\Big[\big(1 - Y\beta^T X\big)^+\Big] = \inf_{\beta\in\mathbb R^d}\Big\{\frac1n\sum_{i=1}^n \big(1 - Y_i\beta^T X_i\big)^+ + \delta\,\|\beta\|_p\Big\}.$$
--
--   The distributionally robust logistic regression and support vector machine over an optimal-transport ball that may move predictors but not labels are therefore exactly the $\ell_p$-norm regularized estimators, with the radius $\delta$ as the regularization parameter.
--
--   **Formalization Note** The theorem is stated per $\beta$ (what the paper's proof establishes) together with the two identities of infima over $\beta$ that the paper prints. The paper prints the support-vector-machine identity without $\inf_\beta$ on the right, although $\beta$ is free there; the reading with $\inf_\beta$ on both sides is used, and the per-$\beta$ identity covers the literal reading as well. The labels $Y_i \in \{-1,+1\}$ come from the setting of Example 2, which Theorem 2 continues. Expectations are lower Lebesgue integrals in $[0,\infty]$, the worst case is a supremum over probability measures $P$ with $D_c(P,P_n) \le \delta$, and couplings are probability measures with both marginals fixed. The $\ell_q$ norm is that of `PiLp q`, so $q = 1$ and $q = \infty$ are included.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 11, Theorem 2; proof in App. A.1, pp. 30–31

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Definitions.Def_RWPI_SqrtLasso_worstCase
import Definitions.Def_RWPI_SqrtLasso_Nq
import Definitions.Def_RWPI_Classif_losses

open MeasureTheory
open scoped ENNReal

namespace RWPI.Classif

/-- Theorem 2, p. 11: with the label-preserving cost `c = N_q` (ρ = 1) and labels
`Yᵢ ∈ {−1, +1}`, for every `δ ≥ 0` and every `β`,
1. `sup_{P : D_c(P, P_n) ≤ δ} E_P[log(1 + e^{−Yβᵀ X})] = (1/n) Σᵢ log(1 + e^{−Yᵢβᵀ Xᵢ}) + δ‖β‖_p`;
2. `sup_{P : D_c(P, P_n) ≤ δ} E_P[(1 − Yβᵀ X)⁺] = (1/n) Σᵢ (1 − Yᵢβᵀ Xᵢ)⁺ + δ‖β‖_p`;
and hence the two identities of infima over `β ∈ ℝ^d` printed in the theorem (with `inf_β` on
both sides of the SVM identity), where `1/p + 1/q = 1`. -/
theorem theorem_2 {d n : ℕ} (hn : 0 < n) (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ)
    (hY : ∀ i, Y i = 1 ∨ Y i = -1) (p q : ℝ≥0∞) (hpq : p.HolderConjugate q)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    (∀ β : Fin d → ℝ,
      RWPI.SqrtLasso.worstCase (RWPI.SqrtLasso.Nq q) δ
          (WassersteinDRO.Regularization.empiricalDistribution (fun i => (X i, Y i)))
          (logLoss β) =
        ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, logLoss β (X i, Y i) + δ * ‖WithLp.toLp p β‖)) ∧
    (∀ β : Fin d → ℝ,
      RWPI.SqrtLasso.worstCase (RWPI.SqrtLasso.Nq q) δ
          (WassersteinDRO.Regularization.empiricalDistribution (fun i => (X i, Y i)))
          (hingeLoss β) =
        ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, hingeLoss β (X i, Y i) + δ * ‖WithLp.toLp p β‖)) ∧
    (⨅ β : Fin d → ℝ,
      RWPI.SqrtLasso.worstCase (RWPI.SqrtLasso.Nq q) δ
          (WassersteinDRO.Regularization.empiricalDistribution (fun i => (X i, Y i)))
          (logLoss β)) =
      (⨅ β : Fin d → ℝ,
        ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, logLoss β (X i, Y i) + δ * ‖WithLp.toLp p β‖)) ∧
    (⨅ β : Fin d → ℝ,
      RWPI.SqrtLasso.worstCase (RWPI.SqrtLasso.Nq q) δ
          (WassersteinDRO.Regularization.empiricalDistribution (fun i => (X i, Y i)))
          (hingeLoss β)) =
      (⨅ β : Fin d → ℝ,
        ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, hingeLoss β (X i, Y i) + δ * ‖WithLp.toLp p β‖)) := by sorry

end RWPI.Classif
