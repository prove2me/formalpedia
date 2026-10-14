-- Prove2me | Theorems.Thm_SCInfoDesign_ValueInfo_deriv_VI_FD_xi
-- name    : SCInfoDesign.ValueInfo.deriv_VI_FD_xi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:27.753687+00:00
-- url     : https://prove2.me/theorems/d5393724-62fd-4db1-984b-30abc1190668
-- title:
--   p. 30, proof of Theorem 2 — ∂(K_F(p₀) − κ(p₀))/∂ξ = (1 − p₀)((a₁ − a₀)/2 + b₀ − b₁ − (a₁ − a₀ + b₀ − b₁)ξ)
-- statement:
--   Let the supports be nested with $a_0<a_1$ ($0\le a_0<a_1<b_1\le b_0$), let $p_0\in(0,1]$ and $\xi\in(0,\underline\tau(p_0))$. Then the value of information against full disclosure, $VI_{FD}(\xi,p_0)=K_F(p_0)-V_\xi(p_0)$ with $K_F(p_0)=(1-p_0)K(0)+p_0K(1)$, is differentiable in $\xi$ with
--   $$\frac{\partial\, VI_{FD}}{\partial\xi}(\xi,p_0)=(1-p_0)\Big(\frac{a_1-a_0}{2}+b_0-b_1-(a_1-a_0+b_0-b_1)\,\xi\Big).$$
--
--   The derivative is positive below and negative above $\xi^*=1-\tfrac12(a_1-a_0)/(b_0-b_1+a_1-a_0)$, which is the unimodality of $VI_{FD}$ in $\xi$ in Theorem 2.
--
--   **Formalization Note** $\kappa(p_0)$ is replaced by the optimal cost $V_\xi(p_0)$, equal to it by (B.2); the derivative is stated on the open interval $\xi\in(0,\underline\tau(p_0))$, the page's interval without its right end, where only a one-sided derivative exists.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 30, proof of Theorem 2 (App. B), third display

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_ValueInfo_Setting

namespace SCInfoDesign.ValueInfo

/-- Display on p. 30 (proof of Theorem 2): for nested supports with `a₀ < a₁`, a prior
`p₀ ∈ (0, 1]` and `ξ ∈ (0, τ̲(p₀))`, the derivative of `VI_FD = K_F(p₀) − κ(p₀)` in `ξ` is
`(1 − p₀)((a₁ − a₀)/2 + b₀ − b₁ − (a₁ − a₀ + b₀ − b₁)ξ)`. -/
theorem deriv_VI_FD_xi
    (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (hlt : P.a₀ < P.a₁) (p₀ : ℝ) (hp₀ : 0 < p₀) (hp₁ : p₀ ≤ 1)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ : ξ < τlow P p₀) :
    HasDerivAt (fun x => VI_FD P x p₀)
      ((1 - p₀) * ((P.a₁ - P.a₀) / 2 + P.b₀ - P.b₁ - (P.a₁ - P.a₀ + P.b₀ - P.b₁) * ξ)) ξ := by sorry

end SCInfoDesign.ValueInfo
