-- Prove2me | Theorems.Thm_SCInfoDesign_Disjoint_eq_C13
-- name    : SCInfoDesign.Disjoint.eq_C13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:57.834729+00:00
-- url     : https://prove2.me/theorems/8d6e7bf5-c199-43de-88d7-8bd550c201de
-- title:
--   (C.13), p. 39 — K_DS jumps down at 1 − ξ: lim_{x→(1−ξ)⁻} K_DS(x) − K_DS(1 − ξ) = (1 − ξ)(a₀ − b₁) > 0
-- statement:
--   In the model with disjoint supports ($a_0<b_0$, $a_1<b_1$, $0\le a_0$, $0\le a_1$, $b_1<a_0$, $0<\xi<1$), let $K_{DS}(p)$ be the retailer's expected shortage at belief $p$ under the supplier's largest optimal quantity. Then the left limit of $K_{DS}$ at $1-\xi$ exists and
--   $$\lim_{x\to(1-\xi)^-}K_{DS}(x)-K_{DS}(1-\xi)=(1-\xi)(a_0-b_1)>0.$$
--
--   The downward jump is what makes the chord from $(0,K_{DS}(0))$ to $(1-\xi,K_{DS}(1-\xi))$ lie below $K_{DS}$ on $[0,1-\xi)$ in the proof of Lemma 3.
--
--   **Formalization Note** The limit is taken from the left within the reals. The jump is positive only when $K_{DS}(1-\xi)$ is evaluated at the retailer-preferred quantity $a_0$; with the quantity $b_1$ printed in Proposition 6, $K_{DS}$ would be left-continuous at $1-\xi$.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 39, (C.13)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Disjoint_Setting

namespace SCInfoDesign.Disjoint

/-- (C.13) (p. 39): `K_DS` jumps down at `1 - ξ`; its left limit exceeds `K_DS(1 - ξ)` by
`(1 - ξ)(a₀ - b₁) > 0`. -/
theorem eq_C13 (P : Params) (hab₀ : P.a₀ < P.b₀) (hab₁ : P.a₁ < P.b₁) (ha₀ : 0 ≤ P.a₀) (ha₁ : 0 ≤ P.a₁)
    (hξ₀ : 0 < P.ξ) (hξ₁ : P.ξ < 1) (hdisj : P.b₁ < P.a₀) :
    Filter.Tendsto P.K (nhdsWithin (1 - P.ξ) (Set.Iio (1 - P.ξ)))
        (nhds (P.K (1 - P.ξ) + (1 - P.ξ) * (P.a₀ - P.b₁))) ∧
      0 < (1 - P.ξ) * (P.a₀ - P.b₁) := by sorry

end SCInfoDesign.Disjoint
