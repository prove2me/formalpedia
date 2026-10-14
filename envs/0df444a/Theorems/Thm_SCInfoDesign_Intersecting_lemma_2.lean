-- Prove2me | Theorems.Thm_SCInfoDesign_Intersecting_lemma_2
-- name    : SCInfoDesign.Intersecting.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:19:07.281987+00:00
-- url     : https://prove2.me/theorems/3068d1a1-bbca-4a50-bf0c-823f795205b1
-- title:
--   Lemma 2, p. 31 — the lower convex envelope κ_IS of K_IS in three regimes of ξ, (C.2)
-- statement:
--   Assume $b_0>b_1>a_0>a_1\ge 0$ and $0<\xi<1$, and with $\delta_u,\delta_d,\delta_{\mathsf{IS}}$ as in Proposition 3 assume $\delta_d>2\delta_u$ and $\delta_{\mathsf{IS}}>\max(\delta_d-2\delta_u,\ \delta_d\delta_u/(\delta_d-2\delta_u))$. Let
--   $$
--   \breve\xi=\frac{\delta_d-2\delta_u}{\delta_d-\delta_u},\qquad \breve p=1-\frac{\xi(b_1-a_1)}{a_0-a_1}.
--   $$
--   Then for every $p\in[0,1]$ the lower convex envelope $\kappa_{\mathsf{IS}}$ of $K_{\mathsf{IS}}$ on $[0,1]$ is
--   $$
--   \kappa_{\mathsf{IS}}(p)=\begin{cases}
--   (1-p)K_{\mathsf{IS}}(0)+pK_{\mathsf{IS}}(1) & \text{if } \xi\in[\breve\xi,1),\\
--   K_{\mathsf{IS}}(p) & \text{if } \xi\in[\underline\tau_{\mathsf{IS}}(0),\breve\xi),\\
--   K_{\mathsf{IS}}(p) \text{ for } p\ge\breve p,\quad \dfrac{p\,(K_{\mathsf{IS}}(\breve p)-K_{\mathsf{IS}}(0))}{\breve p}+K_{\mathsf{IS}}(0) \text{ for } p<\breve p & \text{if } \xi\in(0,\underline\tau_{\mathsf{IS}}(0)).
--   \end{cases}
--   $$
--
--   The lemma identifies the optimal value $\kappa_{\mathsf{IS}}(p_0)$ of the design problem, and so drives the case analysis behind Proposition 3: chord to the endpoints (full disclosure), $K_{\mathsf{IS}}$ itself (no disclosure), and a chord from $0$ to $\breve p$ (partial disclosure).
--
--   **Formalization Note** The paper writes the third case as $K_{\mathsf{IS}}(p)\mathbf 1\{p\ge\breve p\}+(\cdots)\mathbf 1\{p\le\breve p\}$; both indicators equal $1$ at $p=\breve p$, where the two branches agree, so the statement uses the piecewise reading. In the third regime $0<\breve p<1$, so the division by $\breve p$ is never by zero.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 31, Lemma 2, (C.2)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Intersecting_Setting

namespace SCInfoDesign.Intersecting
open BiconvexProg.BranchBound
theorem lemma_2 (P : Params) (ha₁0 : 0 ≤ P.a₁) (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (h2 : 2 * P.δu < P.δd) (hmax : max (P.δd - 2 * P.δu) (P.δd * P.δu / (P.δd - 2 * P.δu)) < P.δIS)
    (p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (P.ξbreve ≤ P.ξ →
      convexEnvelope (Set.Icc (0:ℝ) 1) P.K p = (1 - p) * P.K 0 + p * P.K 1) ∧
    (P.τlowIS 0 ≤ P.ξ → P.ξ < P.ξbreve →
      convexEnvelope (Set.Icc (0:ℝ) 1) P.K p = P.K p) ∧
    (P.ξ < P.τlowIS 0 →
      convexEnvelope (Set.Icc (0:ℝ) 1) P.K p =
        if P.pbreve ≤ p then P.K p
        else p * (P.K P.pbreve - P.K 0) / P.pbreve + P.K 0) := by sorry
end SCInfoDesign.Intersecting
