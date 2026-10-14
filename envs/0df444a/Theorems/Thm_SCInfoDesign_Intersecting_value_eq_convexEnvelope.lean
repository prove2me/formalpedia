-- Prove2me | Theorems.Thm_SCInfoDesign_Intersecting_value_eq_convexEnvelope
-- name    : SCInfoDesign.Intersecting.value_eq_convexEnvelope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:47.24282+00:00
-- url     : https://prove2.me/theorems/a5b44dba-ef78-4e3b-91f9-87e9ac72c507
-- title:
--   (B.2), App. B, p. 25 — the optimal value of (3) is the lower convex envelope κ_IS(p₀) of K_IS (intersecting supports)
-- statement:
--   Assume $b_0>b_1>a_0>a_1\ge 0$ and $0<\xi<1$, and let $p_0\in[0,1]$. Let $K_{\mathsf{IS}}$ be the retailer's cost (B.1) under the supplier's best response, and let $\kappa_{\mathsf{IS}}$ be its lower convex envelope on $[0,1]$, the greatest convex function on $[0,1]$ lying below $K_{\mathsf{IS}}$. Then
--   $$
--   \inf_{\Gamma,\;Q^*\in\mathcal B(\Gamma)}\ \mathbb E\Big[p(D_0-Q^*_p)^+ + (1-p)(D_1-Q^*_p)^+\ \Big|\ \Gamma\Big]=\kappa_{\mathsf{IS}}(p_0),
--   $$
--   where the infimum ranges over all policies on finite message spaces and all best-response profiles. That is, $\kappa_{\mathsf{IS}}(p_0)$ is the greatest lower bound of the achievable values of the design problem (3).
--
--   This is the Kamenica–Gentzkow reduction (their Corollary 2) that the paper invokes in Appendix B and reuses in Appendix C.1; it turns the optimal-policy question into a question about the convex envelope of a one-variable function.
--
--   **Formalization Note** Message spaces are taken to be $\{0,\dots,n-1\}$ for $n\in\mathbb N$, which covers every finite message space up to relabelling. The statement asserts the greatest lower bound, not that it is attained. The envelope is the published definition `BiconvexProg.BranchBound.convexEnvelope` on $\Omega=[0,1]$. The same claim is restated in the sibling missions for their own support configurations, because drafts cannot import one another.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 25, (B.2) and the sentence after it (Corollary 2 of Kamenica and Gentzkow 2011); used for intersecting supports on p. 31

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Intersecting_Setting

namespace SCInfoDesign.Intersecting
open BiconvexProg.BranchBound
theorem value_eq_convexEnvelope (P : Params) (ha₁0 : 0 ≤ P.a₁) (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hb : P.b₁ < P.b₀) (hm : P.a₀ < P.b₁) (ha : P.a₁ < P.a₀)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) :
    IsGLB {c : ℝ | ∃ (n : ℕ) (π : Fin 2 → Fin n → ℝ) (Qs : ℝ → ℝ),
        SCInfoDesign.Nested.IsPolicy π ∧ P.IsBestResponseProfile Qs ∧ c = P.expectedCost p₀ π Qs}
      (convexEnvelope (Set.Icc (0:ℝ) 1) P.K p₀) := by sorry
end SCInfoDesign.Intersecting
