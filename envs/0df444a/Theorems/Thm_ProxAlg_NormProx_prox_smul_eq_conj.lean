-- Prove2me | Theorems.Thm_ProxAlg_NormProx_prox_smul_eq_conj
-- name    : ProxAlg.NormProx.prox_smul_eq_conj
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:34.990979+00:00
-- url     : https://prove2.me/theorems/a97212b7-a6b1-487b-810e-efb59fd73c8c
-- title:
--   (6.7), §6.5, p. 187 — for a norm f on ℝⁿ and λ > 0, prox_{λf}(v) = v − λ prox_{f∗/λ}(v/λ)
-- statement:
--   Let $f=\|\cdot\|$ be a (general) norm on $\mathbb R^n$, not necessarily the Euclidean norm $\|\cdot\|_2$, let $f^*(y)=\sup_x\big(y^Tx-f(x)\big)$ be its convex conjugate, and let $\lambda>0$. With $\operatorname{prox}_{\lambda f}(v)=\operatorname{argmin}_x\big(f(x)+\tfrac1{2\lambda}\|x-v\|_2^2\big)$ as in (1.2) and $f^*/\lambda$ the function $y\mapsto \lambda^{-1}f^*(y)$, for every $v\in\mathbb R^n$
--   $$
--   \operatorname{prox}_{\lambda f}(v)=v-\lambda\operatorname{prox}_{f^*/\lambda}(v/\lambda).
--   $$
--   Equivalently: for all $v,w\in\mathbb R^n$, the point $v-\lambda w$ is $\operatorname{prox}_{\lambda f}(v)$ if and only if $w$ is $\operatorname{prox}_{f^*/\lambda}(v/\lambda)$.
--
--   This is the scaled form of Moreau decomposition (2.4) for a norm; since the conjugate of a norm is the indicator of the dual unit ball, it yields $\operatorname{prox}_{\lambda f}(v)=v-\lambda\Pi_{\mathcal B}(v/\lambda)$.
--
--   **Formalization Note** The page states (6.7) for $f$ a norm, and so does this statement: the norm is a seminorm `N` on `EuclideanSpace ℝ (Fin n)` with definiteness `IsNorm N`, and $f$ is `normFun N`, the map $x\mapsto N(x)$ with values in `EReal`; $f^*$ is the published `conj`. `IsProx g z x` says that $x$ minimizes $u\mapsto\tfrac12\|u-z\|_2^2+g(u)$; with $g=\lambda f$ this objective is $\lambda\big(f(u)+\tfrac1{2\lambda}\|u-z\|_2^2\big)$, which for $\lambda>0$ has the same minimizers as (1.2). The scalings $\lambda f$ and $f^*/\lambda$ are products in `EReal` with the positive reals $\lambda$ and $\lambda^{-1}$, so $+\infty$ stays $+\infty$. The proximal points exist and are unique, so the equivalence for all $w$ is the printed identity.
-- source:
--   Parikh & Boyd, Proximal Algorithms, Found. Trends Optim. 1(3) (2014), §6.5, p. 187, (6.7)

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_ProxAlg_NormProx_Basic

namespace ProxAlg.NormProx

open MoreauProx.Decomposition

theorem prox_smul_eq_conj {n : ℕ} (N : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (hN : IsNorm N) (lam : ℝ) (hlam : 0 < lam) :
    ∀ v w : EuclideanSpace ℝ (Fin n),
      IsProx (fun u => ((lam : ℝ) : EReal) * normFun N u) v (v - lam • w) ↔
        IsProx (fun y => ((lam⁻¹ : ℝ) : EReal) * conj (normFun N) y) (lam⁻¹ • v) w := by sorry

end ProxAlg.NormProx
