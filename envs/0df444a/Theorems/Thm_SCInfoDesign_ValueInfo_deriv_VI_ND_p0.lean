-- Prove2me | Theorems.Thm_SCInfoDesign_ValueInfo_deriv_VI_ND_p0
-- name    : SCInfoDesign.ValueInfo.deriv_VI_ND_p0
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:36.875982+00:00
-- url     : https://prove2.me/theorems/2f71116a-a292-42e3-a4c2-6f2d5ce9f1a9
-- title:
--   p. 30, proof of Theorem 2 — ∂(K(p₀) − κ(p₀))/∂p₀ = (ξ(b₀ − a₀) − p₀²(a₁ − a₀))(2 − ξ)/(2p₀²)
-- statement:
--   Let the supports be nested with $a_0<a_1$ ($0\le a_0<a_1<b_1\le b_0$), let $0<\xi\le\underline\tau(1)=(a_1-a_0)/(b_0-a_0)$ and $\hat p=\xi(b_0-a_0)/(a_1-a_0)$. Then for every prior $p_0\in(\hat p,1)$ the value of information against no disclosure is differentiable in $p_0$ with
--   $$\frac{\partial\, VI_{ND}}{\partial p_0}(\xi,p_0)=\frac{\big(\xi(b_0-a_0)-p_0^2(a_1-a_0)\big)(2-\xi)}{2p_0^2}.$$
--
--   The sign of this derivative changes at $p_0^*=\sqrt{\xi(b_0-a_0)/(a_1-a_0)}$, which is the unimodality claim of Theorem 2.
--
--   **Formalization Note** As in the companion display, $\kappa(p_0)$ is replaced by the optimal cost $V_\xi(p_0)$, equal to it by (B.2). The condition $\xi\le\underline\tau(p_0)$ of the page is, for fixed $\xi$, the condition $p_0\ge\hat p$; the derivative is stated on the open interval $(\hat p,1)$, since $VI_{ND}$ has a kink at $\hat p$ and $p_0=1$ is the end of the domain.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 30, proof of Theorem 2 (App. B), second display

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_ValueInfo_Setting

namespace SCInfoDesign.ValueInfo

/-- Display on p. 30 (proof of Theorem 2): for nested supports with `a₀ < a₁`,
`ξ ∈ (0, τ̲(1)]` and a prior `p₀ ∈ (p̂, 1)`, the derivative of `VI_ND = K(p₀) − κ(p₀)` in `p₀`
is `(ξ(b₀ − a₀) − p₀²(a₁ − a₀))(2 − ξ)/(2p₀²)`. -/
theorem deriv_VI_ND_p0
    (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (hlt : P.a₀ < P.a₁) (ξ : ℝ) (hξ0 : 0 < ξ) (hξ : ξ ≤ τlow P 1)
    (p₀ : ℝ) (hp₀ : pHat P ξ < p₀) (hp₁ : p₀ < 1) :
    HasDerivAt (fun q => VI_ND P ξ q)
      ((ξ * (P.b₀ - P.a₀) - p₀ ^ 2 * (P.a₁ - P.a₀)) * (2 - ξ) / (2 * p₀ ^ 2)) p₀ := by sorry

end SCInfoDesign.ValueInfo
