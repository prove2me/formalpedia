-- Prove2me | Theorems.Thm_SCInfoDesign_Disjoint_eq_C9
-- name    : SCInfoDesign.Disjoint.eq_C9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:46.946848+00:00
-- url     : https://prove2.me/theorems/21eccfc6-66f9-4601-a870-89bd28d331d5
-- title:
--   (C.9), p. 38 — the retailer's cost K_DS(p) in closed form for disjoint supports
-- statement:
--   In the model with disjoint supports ($a_0<b_0$, $a_1<b_1$, $0\le a_0$, $0\le a_1$, $b_1<a_0$, $0<\xi<1$), let $K_{DS}(p)$ be the retailer's expected shortage at belief $p$ when the supplier produces his largest optimal quantity. Then
--   $$K_{DS}(p)=\begin{cases} p\Big(\dfrac{a_0+b_0}{2}-Q^*_p\Big)+\dfrac{1-p}{2(b_1-a_1)}\big(b_1-Q^*_p\big)^2, & 0\le p<1-\xi,\quad Q^*_p=\dfrac{\xi(b_1-a_1)}{1-p}+a_1,\\[2ex] \dfrac{p}{2(b_0-a_0)}\big(b_0-Q^*_p\big)^2, & 1-\xi\le p\le1,\quad Q^*_p=\dfrac{(\xi-1+p)(b_0-a_0)}{p}+a_0.\end{cases}$$
--
--   This closed form is what the envelope computation of Lemma 3 works with.
--
--   **Formalization Note** The paper puts the boundary belief $p=1-\xi$ in the first line, with $Q^*_{1-\xi}=b_1$. With the retailer-preferred best response $Q=a_0$ (the largest optimal quantity at $p=1-\xi$, see Proposition 6) the boundary belongs to the second line, where the formula gives $Q^*_{1-\xi}=a_0$ and $K_{DS}(1-\xi)=(1-\xi)(b_0-a_0)/2$. This is the reading under which (C.13) and Lemma 3 hold.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 38, (C.9)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Disjoint_Setting

namespace SCInfoDesign.Disjoint

/-- (C.9) (p. 38): `K_DS` in closed form, with `Q*_p` of Proposition 6 substituted. The boundary
belief `p = 1 - ξ` is in the second branch, where the retailer-preferred quantity is `a₀`. -/
theorem eq_C9 (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hξ₀ : 0 < P.ξ) (hξ₁ : P.ξ < 1) (hdisj : P.b₁ < P.a₀) :
    (∀ p ∈ Set.Ico (0 : ℝ) (1 - P.ξ),
      P.K p = p * ((P.a₀ + P.b₀) / 2 - (P.ξ * (P.b₁ - P.a₁) / (1 - p) + P.a₁)) +
        (1 - p) / (2 * (P.b₁ - P.a₁)) * (P.b₁ - (P.ξ * (P.b₁ - P.a₁) / (1 - p) + P.a₁)) ^ 2) ∧
    (∀ p ∈ Set.Icc (1 - P.ξ) 1,
      P.K p = p / (2 * (P.b₀ - P.a₀)) *
        (P.b₀ - ((P.ξ - 1 + p) * (P.b₀ - P.a₀) / p + P.a₀)) ^ 2) := by sorry

end SCInfoDesign.Disjoint
