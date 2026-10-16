-- Prove2me | Theorems.Thm_SubsetShrink_BIC_eq_51
-- name    : SubsetShrink.BIC.eq_51
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:37.117748+00:00
-- url     : https://prove2.me/theorems/3e6a6fef-9ee3-4925-96e5-c0b99041d323
-- title:
--   (51), p. 49 — basic inequality for the BIC-type estimator β̂^B_2
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $f^*,\epsilon\in\mathbb R^n$, $y=f^*+\epsilon$ and $a,b\in\mathbb R$. Let $\hat\beta$ be any global minimizer over $\mathbb R^p$ of
--   $\|y-X\beta\|^2+\lambda_\beta\|\beta\|+\mu_\beta\|\beta\|_0$, where $\lambda_\beta=a\sqrt{\|\beta\|_0\log(ep/\|\beta\|_0)}$ and $\mu_\beta=b\log(ep/\|\beta\|_0)$. Then for every $\beta\in\mathbb R^p$,
--   $$\|f^*-X\hat\beta\|^2+\lambda_{\hat\beta}\|\hat\beta\|+\mu_{\hat\beta}\|\hat\beta\|_0\le\|f^*-X\beta\|^2+2\epsilon^\top X(\hat\beta-\beta)+\lambda_\beta\|\beta\|+\mu_\beta\|\beta\|_0 .$$
--
--   This deterministic inequality is the starting point of every bound for $\hat\beta^B_2$: the remaining work is to control the noise term $2\epsilon^\top X(\hat\beta-\beta)$ on high-probability events.
--
--   **Formalization Note** The statement is deterministic: $\epsilon$ is an arbitrary vector and no distributional assumption is used. Products $\mu_\beta\|\beta\|_0$ are `muB b β * l0 β` (value $0$ at $\beta=0$).
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 49, proof of Theorem 5 (B.13), (51)

import Mathlib
import Definitions.Def_SubsetShrink_BIC_Model

namespace SubsetShrink.BIC

open MeasureTheory ProbabilityTheory

/-- (51), p. 49: the basic inequality for a minimizer of the objective of `β̂^B_2`. -/
theorem eq_51 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar ε : Fin n → ℝ) (a b : ℝ)
    (βhat : Fin p → ℝ) (hβhat : IsBIC2 X (fstar + ε) a b βhat) (β : Fin p → ℝ) :
    ∑ i, (fstar i - X.mulVec βhat i) ^ 2 + lamB a βhat * SubsetShrink.Events.l2 βhat + muB b βhat * (SubsetShrink.Events.l0 βhat : ℝ) ≤
      ∑ i, (fstar i - X.mulVec β i) ^ 2 + 2 * SubsetShrink.Events.dot ε (X.mulVec (βhat - β)) +
        lamB a β * SubsetShrink.Events.l2 β + muB b β * (SubsetShrink.Events.l0 β : ℝ) := by sorry

end SubsetShrink.BIC
