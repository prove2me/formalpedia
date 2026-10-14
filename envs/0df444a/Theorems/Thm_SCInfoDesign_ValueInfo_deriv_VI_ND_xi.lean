-- Prove2me | Theorems.Thm_SCInfoDesign_ValueInfo_deriv_VI_ND_xi
-- name    : SCInfoDesign.ValueInfo.deriv_VI_ND_xi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:25.780499+00:00
-- url     : https://prove2.me/theorems/a48319ad-ac1e-4ba0-bf32-252a6daab849
-- title:
--   p. 30, proof of Theorem 2 — ∂(K(p₀) − κ(p₀))/∂ξ = −(1 − p₀)(p₀(a₁ − a₀) + 2(1 − ξ)(b₀ − a₀))/(2p₀) < 0
-- statement:
--   Let the supports be nested with $a_0<a_1$ ($0\le a_0<a_1<b_1\le b_0$), let $p_0\in(0,1]$ and let $\xi\in(0,\underline\tau(p_0))$, where $\underline\tau(p_0)=p_0(a_1-a_0)/(b_0-a_0)$. Then the value of information against no disclosure, $VI_{ND}(\xi,p_0)=K(p_0)-V_\xi(p_0)$, is differentiable in $\xi$ with
--   $$\frac{\partial\, VI_{ND}}{\partial\xi}(\xi,p_0)=-\frac{(1-p_0)\big(p_0(a_1-a_0)+2(1-\xi)(b_0-a_0)\big)}{2p_0},$$
--   and this derivative is negative when $p_0<1$.
--
--   In the proof of Theorem 2 this display gives the claim that $VI_{ND}$ decreases in $\xi$.
--
--   **Formalization Note** The paper writes the derivative of $K(p_0)-\kappa(p_0)$; here the optimal cost $V_\xi(p_0)$ appears, which equals $\kappa(p_0)$ by (B.2). The paper states the display on $(0,\underline\tau(p_0)]$; at $\xi=\underline\tau(p_0)$ only a one-sided derivative exists, so the open interval is used. At $p_0=1$ the derivative is $0$, so the sign claim is restricted to $p_0<1$.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), pp. 29–30, proof of Theorem 2 (App. B), first display on p. 30

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_ValueInfo_Setting

namespace SCInfoDesign.ValueInfo

/-- Display on p. 30 (proof of Theorem 2): for nested supports with `a₀ < a₁`, a prior
`p₀ ∈ (0, 1]` and `ξ ∈ (0, τ̲(p₀))`, the derivative of `VI_ND = K(p₀) − κ(p₀)` in `ξ` is
`−(1 − p₀)(p₀(a₁ − a₀) + 2(1 − ξ)(b₀ − a₀))/(2p₀)`, which is negative when `p₀ < 1`. -/
theorem deriv_VI_ND_xi
    (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (hlt : P.a₀ < P.a₁) (p₀ : ℝ) (hp₀ : 0 < p₀) (hp₁ : p₀ ≤ 1)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ : ξ < τlow P p₀) :
    HasDerivAt (fun x => VI_ND P x p₀)
        (-((1 - p₀) * (p₀ * (P.a₁ - P.a₀) + 2 * (1 - ξ) * (P.b₀ - P.a₀)) / (2 * p₀))) ξ ∧
      (p₀ < 1 →
        -((1 - p₀) * (p₀ * (P.a₁ - P.a₀) + 2 * (1 - ξ) * (P.b₀ - P.a₀)) / (2 * p₀)) < 0) := by sorry

end SCInfoDesign.ValueInfo
