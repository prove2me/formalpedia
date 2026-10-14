-- Prove2me | Theorems.Thm_SCInfoDesign_Disjoint_lemma_3
-- name    : SCInfoDesign.Disjoint.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:54.237046+00:00
-- url     : https://prove2.me/theorems/0954a7ff-ddc3-44c7-beb2-bb06e80507c1
-- title:
--   Lemma 3, p. 38 — the lower convex envelope κ_DS of K_DS: the chord if 2(b₀ − a₀)/(b₁ − a₁) ≥ 1, else the chord to p̃ then K_DS (C.8)
-- statement:
--   In the model with disjoint supports ($a_0<b_0$, $a_1<b_1$, $0\le a_0$, $0\le a_1$, $b_1<a_0$, $0<\xi<1$), let $K_{DS}(p)$ be the retailer's expected shortage at belief $p$ under the supplier's largest optimal quantity, let $\kappa_{DS}$ be its lower convex envelope on $[0,1]$, and let
--   $$\tilde p=\max\Big(1-\xi,\ \frac{2(b_0-a_0)}{b_1-a_1}\Big).$$
--   Then for every $p\in[0,1]$:
--
--   1. if $2(b_0-a_0)/(b_1-a_1)\ge1$, then $\kappa_{DS}(p)=pK_{DS}(1)+(1-p)K_{DS}(0)$;
--   2. if $2(b_0-a_0)/(b_1-a_1)<1$, then
--   $$\kappa_{DS}(p)=\begin{cases}K_{DS}(p), & p\ge\tilde p,\\[1ex] K_{DS}(0)+\dfrac{p\,\big(K_{DS}(\tilde p)-K_{DS}(0)\big)}{\tilde p}, & p<\tilde p.\end{cases}$$
--
--   Together with the value claim after (B.2), this identifies the retailer's optimal cost and, through the shape of $\kappa_{DS}$, the optimal policy of Theorem 3.
--
--   **Formalization Note** $\kappa_{DS}$ is the published `BiconvexProg.BranchBound.convexEnvelope` of $K_{DS}$ over $[0,1]$ (the supremum of convex minorants on $[0,1]$). The result relies on $K_{DS}(1-\xi)$ being evaluated at the retailer-preferred optimal quantity $a_0$; with the quantity $b_1$ printed in Proposition 6 the second case fails whenever $\tilde p=1-\xi$. In the second case $0<\tilde p<1$, so the division by $\tilde p$ is well defined.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 38, Lemma 3, (C.8)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Disjoint_Setting

namespace SCInfoDesign.Disjoint

open BiconvexProg.BranchBound

/-- Lemma 3 (p. 38), display (C.8): the lower convex envelope `κ_DS` of `K_DS` on `[0, 1]`. -/
theorem lemma_3 (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hξ₀ : 0 < P.ξ) (hξ₁ : P.ξ < 1) (hdisj : P.b₁ < P.a₀) :
    (1 ≤ 2 * (P.b₀ - P.a₀) / (P.b₁ - P.a₁) →
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        convexEnvelope (Set.Icc (0 : ℝ) 1) P.K p = p * P.K 1 + (1 - p) * P.K 0) ∧
    (2 * (P.b₀ - P.a₀) / (P.b₁ - P.a₁) < 1 →
      ∀ p ∈ Set.Icc (0 : ℝ) 1,
        convexEnvelope (Set.Icc (0 : ℝ) 1) P.K p =
          if P.ptilde ≤ p then P.K p
          else P.K 0 + p * (P.K P.ptilde - P.K 0) / P.ptilde) := by sorry

end SCInfoDesign.Disjoint
