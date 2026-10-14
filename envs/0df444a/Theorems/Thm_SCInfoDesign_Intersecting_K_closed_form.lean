-- Prove2me | Theorems.Thm_SCInfoDesign_Intersecting_K_closed_form
-- name    : SCInfoDesign.Intersecting.K_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:57.325876+00:00
-- url     : https://prove2.me/theorems/ce0f41cd-c867-4eec-af12-f45625244761
-- title:
--   App. C.1, pp. 32–33 — K_IS(p) in closed form in the three regimes of (6)
-- statement:
--   Assume $b_0>b_1>a_0>a_1\ge 0$ and $0<\xi<1$, and let $p\in[0,1]$. Let $Q^*_p$ be the supplier's optimal quantity, written by the branch of (6) that applies. Then the retailer's cost (B.1) is
--   $$
--   K_{\mathsf{IS}}(p)=\begin{cases}
--   \dfrac{p}{2(b_0-a_0)}(b_0-Q^*_p)^2 & \text{if } \xi\in[\bar\tau_{\mathsf{IS}}(p),1),\\[2mm]
--   \dfrac{p}{2(b_0-a_0)}(b_0-Q^*_p)^2+\dfrac{1-p}{2(b_1-a_1)}(b_1-Q^*_p)^2 & \text{if } \xi\in[\underline\tau_{\mathsf{IS}}(p),\bar\tau_{\mathsf{IS}}(p)],\\[2mm]
--   p\Big(\dfrac{a_0+b_0}{2}-Q^*_p\Big)+\dfrac{1-p}{2(b_1-a_1)}(b_1-Q^*_p)^2 & \text{if } \xi\in(0,\underline\tau_{\mathsf{IS}}(p)],
--   \end{cases}
--   $$
--   with, respectively, $Q^*_p=(\xi-(1-p))(b_0-a_0)/p+a_0$, $Q^*_p=(b_0-a_0)[(b_1-a_1)\xi-(1-p)(a_0-a_1)]/((1-p)(b_0-a_0)+p(b_1-a_1))+a_0$, and $Q^*_p=\xi(b_1-a_1)/(1-p)+a_1$.
--
--   This explicit form of $K_{\mathsf{IS}}$ is the input to every curvature argument in the proof of Lemma 2.
--
--   **Formalization Note** The printed display writes $(b_h-Q^*_p)^2$; $b_h$ is a misprint for $b_0$ (the next display, on p. 33, confirms it), and the statement uses $b_0$. $K_{\mathsf{IS}}$ is the model's (B.1), computed with the supplier's actual best response, not with the closed form.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), pp. 32–33, proof of Lemma 2, display defining K_IS (before (C.3))

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Intersecting_Setting

namespace SCInfoDesign.Intersecting
theorem K_closed_form (P : Params) (ha₁0 : 0 ≤ P.a₁) (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (P.τbarIS p ≤ P.ξ →
      P.K p = p / (2 * (P.b₀ - P.a₀)) * (P.b₀ - P.qHigh p) ^ 2) ∧
    (P.τlowIS p ≤ P.ξ → P.ξ ≤ P.τbarIS p →
      P.K p = p / (2 * (P.b₀ - P.a₀)) * (P.b₀ - P.qMid p) ^ 2 +
        (1 - p) / (2 * (P.b₁ - P.a₁)) * (P.b₁ - P.qMid p) ^ 2) ∧
    (P.ξ ≤ P.τlowIS p →
      P.K p = p * ((P.a₀ + P.b₀) / 2 - P.qLow p) +
        (1 - p) / (2 * (P.b₁ - P.a₁)) * (P.b₁ - P.qLow p) ^ 2) := by sorry
end SCInfoDesign.Intersecting
