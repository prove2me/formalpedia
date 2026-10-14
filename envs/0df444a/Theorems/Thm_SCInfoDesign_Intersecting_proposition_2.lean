-- Prove2me | Theorems.Thm_SCInfoDesign_Intersecting_proposition_2
-- name    : SCInfoDesign.Intersecting.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:52.075931+00:00
-- url     : https://prove2.me/theorems/cccd04df-d542-4a15-9e25-e30dc57f5f40
-- title:
--   Proposition 2, p. 15 — with b₀ > b₁ > a₀ > a₁ the supplier's optimal quantity Q*_p is unique and given by (6)
-- statement:
--   Suppose the demand supports intersect without being nested, $b_0>b_1>a_0>a_1\ge 0$, and let $0<\xi<1$. For a belief $p\in[0,1]$ set
--   $$
--   \bar\tau_{\mathsf{IS}}(p)=1-\frac{p(b_0-b_1)}{b_0-a_0},\qquad \underline\tau_{\mathsf{IS}}(p)=\frac{(1-p)(a_0-a_1)}{b_1-a_1}.
--   $$
--   Then the supplier's problem (2) has a unique optimal quantity $Q^*_p$, and
--   $$
--   Q^*_p=\begin{cases}
--   \dfrac{(\xi-(1-p))(b_0-a_0)}{p}+a_0 & \text{if } \xi\in[\bar\tau_{\mathsf{IS}}(p),1),\\[2mm]
--   \dfrac{(b_0-a_0)\big[(b_1-a_1)\xi-(1-p)(a_0-a_1)\big]}{(1-p)(b_0-a_0)+p(b_1-a_1)}+a_0 & \text{if } \xi\in[\underline\tau_{\mathsf{IS}}(p),\bar\tau_{\mathsf{IS}}(p)],\\[2mm]
--   \dfrac{\xi(b_1-a_1)}{1-p}+a_1 & \text{if } \xi\in(0,\underline\tau_{\mathsf{IS}}(p)].
--   \end{cases}
--   $$
--   In each case, a quantity $Q$ is optimal for (2) if and only if it equals the displayed value.
--
--   This closed form is what turns the retailer's cost $K_{\mathsf{IS}}$ into an explicit function of the belief, on which the envelope analysis of Lemma 2 rests.
--
--   **Formalization Note** Each regime is stated as an equivalence "$Q$ is optimal $\iff Q=\cdot$", which records existence and uniqueness. At $p=0$ the first interval is $[1,1)$, empty, and at $p=1$ the third is $(0,0]$, empty, so the divisions by $p$ and $1-p$ are only reached where they are nonzero. The hypotheses $a_0<b_0$, $a_1<b_1$ and $0\le a_0$ follow from $b_0>b_1>a_0>a_1\ge 0$; $a_1\ge 0$ (nonnegative demand) and $0<\xi<1$ are the paper's implicit standing assumptions.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 15, Proposition 2, (6)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Intersecting_Setting

namespace SCInfoDesign.Intersecting
theorem proposition_2 (P : Params) (ha₁0 : 0 ≤ P.a₁) (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (P.τbarIS p ≤ P.ξ → ∀ Q : ℝ, P.IsOptimalQuantity p Q ↔ Q = P.qHigh p) ∧
    (P.τlowIS p ≤ P.ξ → P.ξ ≤ P.τbarIS p → ∀ Q : ℝ, P.IsOptimalQuantity p Q ↔ Q = P.qMid p) ∧
    (P.ξ ≤ P.τlowIS p → ∀ Q : ℝ, P.IsOptimalQuantity p Q ↔ Q = P.qLow p) := by sorry
end SCInfoDesign.Intersecting
