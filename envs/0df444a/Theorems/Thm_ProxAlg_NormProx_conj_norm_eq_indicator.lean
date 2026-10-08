-- Prove2me | Theorems.Thm_ProxAlg_NormProx_conj_norm_eq_indicator
-- name    : ProxAlg.NormProx.conj_norm_eq_indicator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:31.903547+00:00
-- url     : https://prove2.me/theorems/97c21bbd-a869-4ab3-bbfa-0f23a1589a6a
-- title:
--   §2.5, p. 134 — if f = ‖·‖ is a norm on ℝⁿ then f∗ = I_B, B the unit ball of the dual norm
-- statement:
--   Let $\|\cdot\|$ be a general norm on $\mathbb R^n$ and let $f=\|\cdot\|$. Let $\|z\|_*=\sup\{z^Tx\mid\|x\|\le1\}$ be its dual norm and $\mathcal B=\{x\mid\|x\|_*\le1\}$ the unit ball of the dual norm. Then the convex conjugate $f^*(y)=\sup_x\big(y^Tx-f(x)\big)$ of the norm is the indicator function of $\mathcal B$:
--   $$
--   f^*=I_{\mathcal B},\qquad\text{that is}\qquad \sup_x\big(y^Tx-\|x\|\big)=\begin{cases}0,& \|y\|_*\le 1,\\ +\infty,& \|y\|_*>1,\end{cases}\quad\text{for every } y\in\mathbb R^n .
--   $$
--
--   This is the duality fact that turns the proximal operator of a norm into a projection: combined with Moreau decomposition it gives $\operatorname{prox}_f(v)=v-\Pi_{\mathcal B}(v)$.
--
--   **Formalization Note** The statement is an equality of functions $\mathbb R^n\to$ `EReal` on all of $\mathbb R^n$, with the conjugate taken from the published definition `MoreauProx.Decomposition.conj` ($\sup_x\big(x^Ty-f(x)\big)$, computed in `EReal`). The norm is a seminorm with the definiteness hypothesis `IsNorm N`.
-- source:
--   Parikh & Boyd, Proximal Algorithms, Found. Trends Optim. 1(3) (2014), §2.5, p. 134; restated §6.5, p. 187

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_ProxAlg_NormProx_Basic

namespace ProxAlg.NormProx

open MoreauProx.Decomposition

theorem conj_norm_eq_indicator {n : ℕ} (N : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (hN : IsNorm N) :
    conj (normFun N) = indicator (dualBall N) := by sorry

end ProxAlg.NormProx
