-- Prove2me | Theorems.Thm_SCInfoDesign_ValueInfo_lemma_1
-- name    : SCInfoDesign.ValueInfo.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:27.21947+00:00
-- url     : https://prove2.me/theorems/1748334c-6f6e-4360-ba0b-b63395cdb212
-- title:
--   Lemma 1, p. 25 — the lower convex envelope κ of K in the three regimes of ξ (B.3)
-- statement:
--   Let the supports be nested ($0\le a_0\le a_1<b_1\le b_0$, $a_0<b_0$), let $\xi\in(0,1)$, and let $\kappa$ be the lower convex envelope of the no-disclosure cost $K$ of (B.1) on $[0,1]$. Put $\xi_h=(a_1-a_0)/(b_0-a_0-b_1+a_1)$ and $\hat p=\xi(b_0-a_0)/(a_1-a_0)$. Then for every $p\in[0,1]$:
--
--   1. if $\xi\ge\xi_h$, then $\kappa(p)=pK(1)+(1-p)K(0)$;
--   2. if $(a_1-a_0)/(b_0-a_0)\le\xi\le\xi_h$, then $\kappa(p)=K(p)$;
--   3. if $\xi\le(a_1-a_0)/(b_0-a_0)$, then
--   $$\kappa(p)=\begin{cases}K(p) & p\le\hat p,\\[1mm] \dfrac{K(1)-K(\hat p)}{1-\hat p}(p-\hat p)+K(\hat p) & p>\hat p.\end{cases}$$
--
--   The envelope is the optimal value of the design problem (by (B.2)), so the three regimes are those of full disclosure, no disclosure and the two-message partial policy.
--
--   **Formalization Note** The paper writes case 3 as $K(p)\mathbb 1\{p\le\hat p\}+(\ldots)\mathbb 1\{p\ge\hat p\}$, which double-counts at $p=\hat p$; it is read as the piecewise function, whose branches agree at $\hat p$. When $\hat p=1$ the slope is $0/0$, but the chord branch is then never used. With $a_0=a_1$ the thresholds $(a_1-a_0)/(b_0-a_0)$ and $\xi_h$ are $0$ (with $\xi_h=0/0=0$ for equal supports), cases 2 and 3 are vacuous, and case 1 applies to every $\xi$.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 25, Lemma 1, (B.3)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_ValueInfo_Setting

namespace SCInfoDesign.ValueInfo

/-- Lemma 1 (p. 25): for nested supports and `ξ ∈ (0, 1)`, the lower convex envelope `κ` of `K`
on `[0, 1]` is the chord `pK(1) + (1 − p)K(0)` for `ξ ≥ ξ_h`, `K` itself for
`(a₁ − a₀)/(b₀ − a₀) ≤ ξ ≤ ξ_h`, and, for `ξ ≤ (a₁ − a₀)/(b₀ − a₀)`, `K` up to `p̂` followed by the
chord from `(p̂, K(p̂))` to `(1, K(1))` (the indicators of (B.3) read piecewise). -/
theorem lemma_1
    (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    ((P.a₁ - P.a₀) / (P.b₀ - P.a₀ - P.b₁ + P.a₁) ≤ ξ →
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        BiconvexProg.BranchBound.convexEnvelope (Set.Icc (0 : ℝ) 1) (K P ξ) p =
          p * K P ξ 1 + (1 - p) * K P ξ 0) ∧
    ((P.a₁ - P.a₀) / (P.b₀ - P.a₀) ≤ ξ → ξ ≤ (P.a₁ - P.a₀) / (P.b₀ - P.a₀ - P.b₁ + P.a₁) →
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        BiconvexProg.BranchBound.convexEnvelope (Set.Icc (0 : ℝ) 1) (K P ξ) p = K P ξ p) ∧
    (ξ ≤ (P.a₁ - P.a₀) / (P.b₀ - P.a₀) →
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        BiconvexProg.BranchBound.convexEnvelope (Set.Icc (0 : ℝ) 1) (K P ξ) p =
          if p ≤ pHat P ξ then K P ξ p
          else (K P ξ 1 - K P ξ (pHat P ξ)) / (1 - pHat P ξ) * (p - pHat P ξ) +
            K P ξ (pHat P ξ)) := by sorry

end SCInfoDesign.ValueInfo
