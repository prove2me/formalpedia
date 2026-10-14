-- Prove2me | Theorems.Thm_SCInfoDesign_Nested_lemma_1
-- name    : SCInfoDesign.Nested.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:09.733469+00:00
-- url     : https://prove2.me/theorems/4460ed93-f7ed-40a7-87c6-0ce24ad6887b
-- title:
--   Lemma 1, p. 25 — the lower convex envelope κ of K in the three regimes (B.3)
-- statement:
--   In the nested-support model ($0\le a_0\le a_1<b_1\le b_0$, $a_0<b_0$, $0<\xi<1$) let $K$ be the retailer's cost (B.1) and $\kappa$ its lower convex envelope on $[0,1]$. Write $\xi_h=(a_1-a_0)/(b_0-a_0-b_1+a_1)$ and $\hat p=\xi(b_0-a_0)/(a_1-a_0)$. Then for every $p\in[0,1]$:
--
--   1. if $\xi\in[\xi_h,1)$, then $\kappa(p)=pK(1)+(1-p)K(0)$;
--   2. if $\xi\in\big[\tfrac{a_1-a_0}{b_0-a_0},\xi_h\big]$, then $\kappa(p)=K(p)$;
--   3. if $\xi\in\big(0,\tfrac{a_1-a_0}{b_0-a_0}\big]$, then
--   $$\kappa(p)=\begin{cases}K(p) & p\le\hat p,\\[1mm] \dfrac{K(1)-K(\hat p)}{1-\hat p}\,(p-\hat p)+K(\hat p) & p>\hat p.\end{cases}$$
--
--   The lemma computes the convex envelope that, by the Kamenica–Gentzkow reduction, equals the retailer's optimal cost; the posteriors that attain it give the optimal policy of Theorem 1.
--
--   **Formalization Note** The paper prints case 3 as $K(p)\mathbb 1_{\{p\le\hat p\}}+(\ldots)\mathbb 1_{\{p\ge\hat p\}}$; at $p=\hat p$ both indicators equal $1$ and the printed value would be $2K(\hat p)$. The intended piecewise function is formalized (the two branches agree at $\hat p$). When $\hat p=1$ (that is, $\xi=(a_1-a_0)/(b_0-a_0)$) the slope is $0/0$ in Lean, but the line branch is used only for $p>1$, which never occurs in $[0,1]$. The envelope is the published `convexEnvelope` on $[0,1]$. The thresholds are $0/0=0$ in Lean when the supports coincide; when $a_0=a_1$, cases 2 and 3 are empty under $\xi>0$ and case 1 holds for every $\xi$, as in the paper (Corollary 2).
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), App. B, p. 25, Lemma 1, (B.3)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Nested_Setting

namespace SCInfoDesign.Nested
open BiconvexProg.BranchBound
theorem lemma_1 (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀) :
    (P.ξh ≤ P.ξ → ∀ p ∈ Set.Icc (0:ℝ) 1,
      convexEnvelope (Set.Icc (0:ℝ) 1) P.K p = p * P.K 1 + (1 - p) * P.K 0) ∧
    ((P.a₁ - P.a₀) / (P.b₀ - P.a₀) ≤ P.ξ → P.ξ ≤ P.ξh → ∀ p ∈ Set.Icc (0:ℝ) 1,
      convexEnvelope (Set.Icc (0:ℝ) 1) P.K p = P.K p) ∧
    (P.ξ ≤ (P.a₁ - P.a₀) / (P.b₀ - P.a₀) → ∀ p ∈ Set.Icc (0:ℝ) 1,
      convexEnvelope (Set.Icc (0:ℝ) 1) P.K p =
        if p ≤ P.pHat then P.K p
        else (P.K 1 - P.K P.pHat) / (1 - P.pHat) * (p - P.pHat) + P.K P.pHat) := by sorry
end SCInfoDesign.Nested
