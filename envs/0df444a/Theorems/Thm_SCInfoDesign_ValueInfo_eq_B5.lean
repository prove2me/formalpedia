-- Prove2me | Theorems.Thm_SCInfoDesign_ValueInfo_eq_B5
-- name    : SCInfoDesign.ValueInfo.eq_B5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:34.016694+00:00
-- url     : https://prove2.me/theorems/0ee1ef1c-bf38-409e-9905-1d3aed5d0c55
-- title:
--   (B.5), p. 28 — K in closed form for ξ ∈ (0, (a₁ − a₀)/(b₀ − a₀)]
-- statement:
--   Let the supports be nested ($0\le a_0\le a_1<b_1\le b_0$, $a_0<b_0$) and let $0<\xi\le (a_1-a_0)/(b_0-a_0)$. Put $\hat p=\xi(b_0-a_0)/(a_1-a_0)$. Then for every belief $p\in[0,1]$ the no-disclosure cost $K(p)$ of (B.1) is
--   $$K(p)=\begin{cases}\dfrac{p}{b_0-a_0}\dfrac{(b_0-Q^*_p)^2}{2}+\dfrac{1-p}{b_1-a_1}\dfrac{(b_1-Q^*_p)^2}{2} & p\le\hat p,\\[3mm] \dfrac{p}{b_0-a_0}\dfrac{(b_0-Q^*_p)^2}{2}+(1-p)\Big[\dfrac{b_1+a_1}{2}-Q^*_p\Big] & p>\hat p,\end{cases}$$
--   where, by (B.4), $Q^*_p=\dfrac{b_1(\xi-\underline\tau(p))+a_1(\bar\tau(p)-\xi)}{\bar\tau(p)-\underline\tau(p)}$ for $p\le\hat p$ and $Q^*_p=\dfrac{\xi(b_0-a_0)}{p}+a_0$ for $p>\hat p$.
--
--   The first branch is the function $\hat K(p)$ of p. 27. This closed form is the input of Lemma 1 and of every derivative computed in the proof of Theorem 2.
--
--   **Formalization Note** The right-hand side is written with $Q^*_p$ substituted, so it is a closed form in $p$; $K$ itself is defined from the argmin of (2), not from these formulas. The paper's two branches are both closed at $\hat p$ and agree there; the formalization assigns $p=\hat p$ to the first branch. The hypothesis on $\xi$ forces $a_0<a_1$, so $\hat p$ is well defined, and $\hat p>0$, so the second branch never divides by $0$.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 28, (B.4)–(B.5); K̂ from p. 27

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_ValueInfo_Setting

namespace SCInfoDesign.ValueInfo

/-- (B.5) with (B.4) substituted (App. B, p. 28): for nested supports and
`ξ ∈ (0, (a₁ − a₀)/(b₀ − a₀)]`, the retailer's no-disclosure cost `K(p)` in closed form. -/
theorem eq_B5
    (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ : ξ ≤ (P.a₁ - P.a₀) / (P.b₀ - P.a₀)) :
    ∀ p ∈ Set.Icc (0 : ℝ) 1,
      K P ξ p =
        if p ≤ pHat P ξ then
          (let Q := (P.b₁ * (ξ - τlow P p) + P.a₁ * (τup P p - ξ)) / (τup P p - τlow P p)
           p / (P.b₀ - P.a₀) * ((P.b₀ - Q) ^ 2 / 2) +
             (1 - p) / (P.b₁ - P.a₁) * ((P.b₁ - Q) ^ 2 / 2))
        else
          (let Q := ξ * (P.b₀ - P.a₀) / p + P.a₀
           p / (P.b₀ - P.a₀) * ((P.b₀ - Q) ^ 2 / 2) +
             (1 - p) * ((P.b₁ + P.a₁) / 2 - Q)) := by sorry

end SCInfoDesign.ValueInfo
