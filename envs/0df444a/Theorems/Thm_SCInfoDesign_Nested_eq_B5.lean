-- Prove2me | Theorems.Thm_SCInfoDesign_Nested_eq_B5
-- name    : SCInfoDesign.Nested.eq_B5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:28:59.159687+00:00
-- url     : https://prove2.me/theorems/83cb2a84-176d-4e28-9f96-0038ca040a2b
-- title:
--   (B.5), App. B, p. 28 — K(p) in closed form when ξ ≤ (a₁ − a₀)/(b₀ − a₀)
-- statement:
--   In the nested-support model ($0\le a_0\le a_1<b_1\le b_0$, $a_0<b_0$, $0<\xi<1$) suppose
--   $$\xi\le\frac{a_1-a_0}{b_0-a_0},$$
--   and let $\hat p=\xi(b_0-a_0)/(a_1-a_0)$, $\underline\tau(p)=p(a_1-a_0)/(b_0-a_0)$, $\bar\tau(p)=1-p(b_0-b_1)/(b_0-a_0)$. Then for $p\in[0,1]$ the retailer's cost $K(p)$ of (B.1) is
--   $$K(p)=\begin{cases}\dfrac{p}{b_0-a_0}\dfrac{(b_0-Q_p)^2}{2}+\dfrac{1-p}{b_1-a_1}\dfrac{(b_1-Q_p)^2}{2}\ \text{ with } Q_p=\dfrac{b_1(\xi-\underline\tau(p))+a_1(\bar\tau(p)-\xi)}{\bar\tau(p)-\underline\tau(p)}, & p\le\hat p,\\[3mm] \dfrac{p}{b_0-a_0}\dfrac{(b_0-Q_p)^2}{2}+(1-p)\Big[\dfrac{b_1+a_1}{2}-Q_p\Big]\ \text{ with } Q_p=\dfrac{\xi(b_0-a_0)}{p}+a_0, & p\ge\hat p.\end{cases}$$
--
--   This closed form of $K$ in the low-critical-ratio regime is what identifies the shape of the envelope in the third case of Lemma 1.
--
--   **Formalization Note** The supplier's quantity $Q^*_p$ of (B.4) is substituted, so each right-hand side is an explicit function of $p$; the first branch is the paper's $\hat K(p)$ (p. 27). Both closed intervals are kept as printed; the branches agree at $p=\hat p$. The hypotheses force $a_0<a_1$ (if $a_0=a_1$ the case $0<\xi\le 0$ is empty), so $\hat p>0$ and the division by $p$ in the second branch happens only at $p\ge\hat p>0$.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), App. B, p. 28, (B.4)–(B.5); p. 27, definition of K̂

import Mathlib
import Definitions.Def_SCInfoDesign_Nested_Setting

namespace SCInfoDesign.Nested
theorem eq_B5 (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (hξ_le : P.ξ ≤ (P.a₁ - P.a₀) / (P.b₀ - P.a₀))
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (p ≤ P.pHat →
      P.K p =
        p / (P.b₀ - P.a₀) *
            (P.b₀ - (P.b₁ * (P.ξ - P.τlow p) + P.a₁ * (P.τup p - P.ξ)) / (P.τup p - P.τlow p)) ^ 2 / 2 +
          (1 - p) / (P.b₁ - P.a₁) *
            (P.b₁ - (P.b₁ * (P.ξ - P.τlow p) + P.a₁ * (P.τup p - P.ξ)) / (P.τup p - P.τlow p)) ^ 2 / 2) ∧
    (P.pHat ≤ p →
      P.K p =
        p / (P.b₀ - P.a₀) * (P.b₀ - (P.ξ * (P.b₀ - P.a₀) / p + P.a₀)) ^ 2 / 2 +
          (1 - p) * ((P.b₁ + P.a₁) / 2 - (P.ξ * (P.b₀ - P.a₀) / p + P.a₀))) := by sorry
end SCInfoDesign.Nested
