-- Prove2me | Theorems.Thm_SCInfoDesign_Nested_value_eq_convexEnvelope
-- name    : SCInfoDesign.Nested.value_eq_convexEnvelope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:26.763048+00:00
-- url     : https://prove2.me/theorems/dbd94c26-05ce-4b4c-9397-d70a0179d946
-- title:
--   (B.2) value claim, App. B, p. 25 — the optimal value of (3) is κ(p₀), the lower convex envelope of K at p₀
-- statement:
--   In the nested-support model ($0\le a_0\le a_1<b_1\le b_0$, $a_0<b_0$, $0<\xi<1$), let $K(p)$ be the retailer's expected shortage (B.1) when both firms hold belief $p$ and the supplier produces his optimal quantity, and let
--   $$\kappa(x)=\sup\{g(x)\;:\;g \text{ convex on }[0,1],\ g\le K \text{ on }[0,1]\}$$
--   be the lower convex envelope of $K$ on $[0,1]$. Then for every prior $p_0\in[0,1]$, $\kappa(p_0)$ is the infimum of the retailer's objective (3),
--   $$\kappa(p_0)=\inf\Big\{\mathbb E\big[p(D_0-Q^*_p)^+ + (1-p)(D_1-Q^*_p)^+\mid\Gamma\big]\;:\;\Gamma \text{ a policy},\ Q^*\in\mathcal B(\Gamma)\Big\},$$
--   where policies range over all finite message spaces.
--
--   This is the Kamenica–Gentzkow reduction that the paper invokes (their Corollary 2): the retailer's problem becomes the computation of a convex envelope, which Lemma 1 then carries out.
--
--   **Formalization Note** The infimum is stated as `IsGLB` of the set of attainable objective values over policies on `Fin n` for all `n`, which represent every finite message space up to relabelling. The envelope is the published definition `BiconvexProg.BranchBound.convexEnvelope` on $[0,1]$, the greatest convex minorant, which on $[0,1]$ coincides with the paper's $\kappa(x)=\inf\{y:(x,y)\in\mathrm{co}(K)\}$.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), App. B, p. 25, (B.2) and the sentence after it (Kamenica–Gentzkow Corollary 2), definition of κ

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Nested_Setting

namespace SCInfoDesign.Nested
open BiconvexProg.BranchBound
theorem value_eq_convexEnvelope (P : Params)
    (ha : P.a₀ < P.b₀) (ha₁ : P.a₁ < P.b₁) (ha₀0 : 0 ≤ P.a₀) (ha₁0 : 0 ≤ P.a₁)
    (hξ0 : 0 < P.ξ) (hξ1 : P.ξ < 1)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0:ℝ) 1) :
    IsGLB {c : ℝ | ∃ (n : ℕ) (π : Fin 2 → Fin n → ℝ) (Qs : ℝ → ℝ),
        IsPolicy π ∧ P.IsBestResponseProfile Qs ∧ c = P.expectedCost p₀ π Qs}
      (convexEnvelope (Set.Icc (0:ℝ) 1) P.K p₀) := by sorry
end SCInfoDesign.Nested
