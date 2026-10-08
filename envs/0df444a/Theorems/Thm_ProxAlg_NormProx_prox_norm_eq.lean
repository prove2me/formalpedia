-- Prove2me | Theorems.Thm_ProxAlg_NormProx_prox_norm_eq
-- name    : ProxAlg.NormProx.prox_norm_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:21.782815+00:00
-- url     : https://prove2.me/theorems/ba1ede94-ac59-4c69-8f2c-b84bd70bc433
-- title:
--   (6.8), §6.5, p. 187 — for a norm f on ℝⁿ and λ > 0, prox_{λf}(v) = v − λΠ_B(v/λ), B the dual-norm unit ball
-- statement:
--   Let $\|\cdot\|$ be a general norm on $\mathbb R^n$ and $f=\|\cdot\|$. Let $\|z\|_*=\sup\{z^Tx\mid\|x\|\le1\}$ be the dual norm and $\mathcal B=\{x\mid\|x\|_*\le1\}$ its unit ball, and write $\Pi_{\mathcal B}(u)=\operatorname{argmin}_{x\in\mathcal B}\|x-u\|_2$ for the Euclidean projection onto $\mathcal B$. For every $\lambda>0$ and every $v\in\mathbb R^n$, the proximal operator $\operatorname{prox}_{\lambda f}(v)=\operatorname{argmin}_x\big(\|x\|+\tfrac1{2\lambda}\|x-v\|_2^2\big)$ is
--   $$
--   \operatorname{prox}_{\lambda f}(v)=v-\lambda\,\Pi_{\mathcal B}(v/\lambda).
--   $$
--   Equivalently: for all $v,w\in\mathbb R^n$, the point $v-\lambda w$ is $\operatorname{prox}_{\lambda f}(v)$ if and only if $w$ is $\Pi_{\mathcal B}(v/\lambda)$.
--
--   Evaluating the proximal operator of any norm thus reduces to projecting onto the unit ball of its dual norm. For the Euclidean norm this gives block soft thresholding, and for the $\ell_1$ norm soft thresholding.
--
--   **Formalization Note** The norm is a Mathlib seminorm `N` on `EuclideanSpace ℝ (Fin n)` with the definiteness hypothesis `IsNorm N`; it is not the Euclidean norm, which remains the norm of the proximal objective (1.1) and of the projection (1.3). `IsProx g z x` says $x$ minimizes $u\mapsto\tfrac12\|u-z\|_2^2+g(u)$; with $g=\lambda f$ this is $\lambda\big(f(u)+\tfrac1{2\lambda}\|u-z\|_2^2\big)$, which has the same minimizers as (1.2) because $\lambda>0$. `IsProj (dualBall N) u w` says $w\in\mathcal B$ is a point of $\mathcal B$ nearest to $u$. Both minimizers exist and are unique, and every $x$ has the form $v-\lambda w$, so the equivalence over $w$ is the printed equation. The dual ball is defined through the printed supremum, not by a closed form.
-- source:
--   Parikh & Boyd, Proximal Algorithms, Found. Trends Optim. 1(3) (2014), §6.5, p. 187, (6.7)–(6.8)

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_ProxAlg_NormProx_Basic

namespace ProxAlg.NormProx

open MoreauProx.Decomposition

theorem prox_norm_eq {n : ℕ} (N : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) (hN : IsNorm N)
    (lam : ℝ) (hlam : 0 < lam) :
    ∀ v w : EuclideanSpace ℝ (Fin n),
      IsProx (fun u => ((lam : ℝ) : EReal) * normFun N u) v (v - lam • w) ↔
        IsProj (dualBall N) (lam⁻¹ • v) w := by sorry

end ProxAlg.NormProx
