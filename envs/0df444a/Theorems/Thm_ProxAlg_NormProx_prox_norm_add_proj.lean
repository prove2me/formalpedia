-- Prove2me | Theorems.Thm_ProxAlg_NormProx_prox_norm_add_proj
-- name    : ProxAlg.NormProx.prox_norm_add_proj
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:23.573471+00:00
-- url     : https://prove2.me/theorems/c7a4153e-8f99-40db-80f6-3ef7a993d9bd
-- title:
--   §2.5, p. 134 — for a norm f on ℝⁿ, v = prox_f(v) + Π_B(v)
-- statement:
--   Let $\|\cdot\|$ be a general norm on $\mathbb R^n$, $f=\|\cdot\|$, and $\mathcal B=\{x\mid\|x\|_*\le1\}$ the unit ball of the dual norm $\|z\|_*=\sup\{z^Tx\mid\|x\|\le1\}$. Write $\operatorname{prox}_f(v)=\operatorname{argmin}_x\big(f(x)+\tfrac12\|x-v\|_2^2\big)$ and $\Pi_{\mathcal B}(v)=\operatorname{argmin}_{x\in\mathcal B}\|x-v\|_2$ for the Euclidean projection onto $\mathcal B$. Then for every $v\in\mathbb R^n$
--   $$
--   v=\operatorname{prox}_f(v)+\Pi_{\mathcal B}(v).
--   $$
--   Equivalently: for all $v,x\in\mathbb R^n$, the point $x$ is $\operatorname{prox}_f(v)$ if and only if $v-x$ is $\Pi_{\mathcal B}(v)$.
--
--   So the proximal operator of a norm can be evaluated by projecting onto the unit ball of the dual norm, and vice versa.
--
--   **Formalization Note** Both operators are stated as predicates: `IsProx (normFun N) v x` says that $x$ minimizes $u\mapsto\tfrac12\|u-v\|_2^2+\|u\|$, and `IsProj (dualBall N) v y` says that $y\in\mathcal B$ is a point of $\mathcal B$ nearest to $v$ in the Euclidean norm. The minimizer and the projection both exist and are unique (the norm is closed proper convex; $\mathcal B$ is nonempty, closed and convex), so the equivalence for all $x$ is the printed identity. The norm in the proximal objective is the Euclidean one, as in (1.1); the general norm enters only through $f$ and $\mathcal B$.
-- source:
--   Parikh & Boyd, Proximal Algorithms, Found. Trends Optim. 1(3) (2014), §2.5, p. 134 (display after 'By Moreau decomposition, this implies that')

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_ProxAlg_NormProx_Basic

namespace ProxAlg.NormProx

open MoreauProx.Decomposition

theorem prox_norm_add_proj {n : ℕ} (N : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (hN : IsNorm N) :
    ∀ v x : EuclideanSpace ℝ (Fin n),
      IsProx (normFun N) v x ↔ IsProj (dualBall N) v (v - x) := by sorry

end ProxAlg.NormProx
