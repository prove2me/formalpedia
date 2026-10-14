-- Prove2me | Theorems.Thm_SCInfoDesign_Nested_proposition_1
-- name    : SCInfoDesign.Nested.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:00.732503+00:00
-- url     : https://prove2.me/theorems/67581c75-2196-460c-b88d-a1f6424ca248
-- title:
--   Proposition 1, p. 8 — the supplier's optimal quantity Q*_p is unique and given by (4)
-- statement:
--   Consider the nested-support model: $0\le a_0\le a_1<b_1\le b_0$ with $a_0<b_0$, and a critical ratio $\xi\in(0,1)$. Let $p\in[0,1]$ be the supplier's belief that $\omega=0$, and write
--   $$\underline\tau(p)=\frac{p(a_1-a_0)}{b_0-a_0},\qquad \bar\tau(p)=1-\frac{p(b_0-b_1)}{b_0-a_0}.$$
--   Then the supplier's newsvendor problem (2) has a unique optimal quantity $Q^*_p$, namely
--   $$Q^*_p=\begin{cases} b_0-\dfrac{(b_0-a_0)(1-\xi)}{p} & \xi\in[\bar\tau(p),1],\\[2mm] \dfrac{b_1(\xi-\underline\tau(p))+a_1(\bar\tau(p)-\xi)}{\bar\tau(p)-\underline\tau(p)} & \xi\in[\underline\tau(p),\bar\tau(p)],\\[2mm] \dfrac{\xi(b_0-a_0)}{p}+a_0 & \xi\in[0,\underline\tau(p)].\end{cases}$$
--   In each case, a quantity $Q$ is optimal for (2) at belief $p$ if and only if it equals the displayed value.
--
--   The proposition gives the supplier's best response in closed form. It shows that the best-response set $\mathcal B(\Gamma)$ is a singleton, so the retailer's design problem reduces to choosing a distribution of posteriors.
--
--   **Formalization Note** Each case is stated as an equivalence ($Q$ optimal $\iff$ $Q=\ldots$), which expresses both existence and uniqueness. The hypotheses $0\le a_0$, $0\le a_1$ (demand is nonnegative) are added: without them the constraint $Q\ge 0$ could bind. At $p=0$ the first case needs $\xi=1$ and the third $\xi=0$, both excluded by $0<\xi<1$, so no division by $p=0$ occurs; $\bar\tau(p)-\underline\tau(p)>0$ for every $p\in[0,1]$.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 8, Proposition 1, (4)

import Mathlib
import Definitions.Def_SCInfoDesign_Nested_Setting

namespace SCInfoDesign.Nested
theorem proposition_1 (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (P.ξ ∈ Set.Icc (P.τup p) 1 →
      ∀ Q, P.IsOptimalQuantity p Q ↔ Q = P.b₀ - (P.b₀ - P.a₀) * (1 - P.ξ) / p) ∧
    (P.ξ ∈ Set.Icc (P.τlow p) (P.τup p) →
      ∀ Q, P.IsOptimalQuantity p Q ↔
        Q = (P.b₁ * (P.ξ - P.τlow p) + P.a₁ * (P.τup p - P.ξ)) / (P.τup p - P.τlow p)) ∧
    (P.ξ ∈ Set.Icc 0 (P.τlow p) →
      ∀ Q, P.IsOptimalQuantity p Q ↔ Q = P.ξ * (P.b₀ - P.a₀) / p + P.a₀) := by sorry
end SCInfoDesign.Nested
