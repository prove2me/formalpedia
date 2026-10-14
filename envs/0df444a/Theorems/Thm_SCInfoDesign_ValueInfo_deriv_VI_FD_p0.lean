-- Prove2me | Theorems.Thm_SCInfoDesign_ValueInfo_deriv_VI_FD_p0
-- name    : SCInfoDesign.ValueInfo.deriv_VI_FD_p0
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:54.674202+00:00
-- url     : https://prove2.me/theorems/6ad0b211-56ca-4fcf-9fef-d3979d1517f5
-- title:
--   p. 30, proof of Theorem 2 — ∂(K_F(p₀) − κ(p₀))/∂p₀ = −[(a₁ − a₀)(1 − ξ) + (b₀ − b₁)(2 − ξ)]ξ/2 < 0
-- statement:
--   Let the supports be nested with $a_0<a_1$ ($0\le a_0<a_1<b_1\le b_0$), let $0<\xi\le\underline\tau(1)$ and $\hat p=\xi(b_0-a_0)/(a_1-a_0)$. Then for every prior $p_0\in(\hat p,1)$ the value of information against full disclosure is differentiable in $p_0$ with
--   $$\frac{\partial\, VI_{FD}}{\partial p_0}(\xi,p_0)=-\frac{\big[(a_1-a_0)(1-\xi)+(b_0-b_1)(2-\xi)\big]\xi}{2}<0.$$
--
--   This gives the claim of Theorem 2 that $VI_{FD}$ decreases in $p_0$.
--
--   **Formalization Note** $\kappa(p_0)$ is replaced by the optimal cost $V_\xi(p_0)$, equal to it by (B.2); the derivative is stated on the open interval $(\hat p,1)$ of priors in the regime $\xi\le\underline\tau(p_0)$.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 30, proof of Theorem 2 (App. B), fourth display

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_ValueInfo_Setting

namespace SCInfoDesign.ValueInfo

/-- Display on p. 30 (proof of Theorem 2): for nested supports with `a₀ < a₁`,
`ξ ∈ (0, τ̲(1)]` and a prior `p₀ ∈ (p̂, 1)`, the derivative of `VI_FD = K_F(p₀) − κ(p₀)` in
`p₀` is `−[(a₁ − a₀)(1 − ξ) + (b₀ − b₁)(2 − ξ)]ξ/2`, which is negative. -/
theorem deriv_VI_FD_p0
    (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (hlt : P.a₀ < P.a₁) (ξ : ℝ) (hξ0 : 0 < ξ) (hξ : ξ ≤ τlow P 1)
    (p₀ : ℝ) (hp₀ : pHat P ξ < p₀) (hp₁ : p₀ < 1) :
    HasDerivAt (fun q => VI_FD P ξ q)
        (-(((P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ)) * ξ) / 2) p₀ ∧
      -(((P.a₁ - P.a₀) * (1 - ξ) + (P.b₀ - P.b₁) * (2 - ξ)) * ξ) / 2 < 0 := by sorry

end SCInfoDesign.ValueInfo
