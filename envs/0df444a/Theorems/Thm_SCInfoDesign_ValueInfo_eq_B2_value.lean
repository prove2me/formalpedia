-- Prove2me | Theorems.Thm_SCInfoDesign_ValueInfo_eq_B2_value
-- name    : SCInfoDesign.ValueInfo.eq_B2_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:33.691718+00:00
-- url     : https://prove2.me/theorems/69cf038a-fa34-473d-b1aa-c6d87aa1b6c0
-- title:
--   (B.2), p. 25 — the optimal value of the design problem (3) is κ(p₀), the lower convex envelope of K
-- statement:
--   Under nested supports ($0\le a_0\le a_1<b_1\le b_0$, $a_0<b_0$), for every critical ratio $\xi\in(0,1)$ and every prior $p_0\in[0,1]$, the optimal expected cost of the retailer's information design problem (3), taken over all finite disclosure policies and all best-response profiles of the supplier, equals
--   $$V_\xi(p_0)=\kappa(p_0),$$
--   where $\kappa$ is the lower convex envelope of the no-disclosure cost $K$ of (B.1) on $[0,1]$: the largest convex function on $[0,1]$ lying below $K$.
--
--   This is the concavification reduction of Kamenica and Gentzkow (2011, Corollary 2), which the paper invokes after (B.2) to turn every question about optimal policies into a question about $\kappa$.
--
--   **Formalization Note** $\kappa$ is the published `BiconvexProg.BranchBound.convexEnvelope` on $\Omega=[0,1]$, the supremum of all convex minorants of $K$ on $[0,1]$; on $[0,1]$ this is the paper's $\kappa(x)=\inf\{y\mid (x,y)\in\mathrm{co}(K)\}$. The optimal value is the infimum (`sInf`) defined in the Setting. This statement restates, for the parametrization of this mission, the value claim of mission I.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 25, (B.2) and the claim after it (App. B)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_ValueInfo_Setting

namespace SCInfoDesign.ValueInfo

/-- (B.2) value claim (App. B, p. 25, via Kamenica–Gentzkow 2011, Corollary 2): for nested
supports, the optimal value of the retailer's design problem (3) is `κ(p₀)`, the lower convex
envelope of `K` on `[0, 1]` evaluated at the prior. -/
theorem eq_B2_value
    (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hnest_a : P.a₀ ≤ P.a₁) (hnest_b : P.b₁ ≤ P.b₀)
    (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (p₀ : ℝ) (hp₀ : p₀ ∈ Set.Icc (0 : ℝ) 1) :
    optimalCost P ξ p₀ =
      BiconvexProg.BranchBound.convexEnvelope (Set.Icc (0 : ℝ) 1) (K P ξ) p₀ := by sorry

end SCInfoDesign.ValueInfo
