-- Prove2me | Theorems.Thm_SCInfoDesign_Intersecting_hypotheses_equiv
-- name    : SCInfoDesign.Intersecting.hypotheses_equiv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:48.072493+00:00
-- url     : https://prove2.me/theorems/cc2245a0-bb6e-4111-b87d-2e5c958c0297
-- title:
--   App. C.1, p. 32 — δ_d > 2δ_u and δ_IS > max(δ_d − 2δ_u, δ_dδ_u/(δ_d − 2δ_u)) iff τ̄_IS(1) > ξ̆ > τ̲_IS(0)
-- statement:
--   Let $\delta_u=b_0-b_1$, $\delta_d=a_0-a_1$ and $\delta_{\mathsf{IS}}=b_1-a_0$ all be positive, so that the supports intersect but are not nested. Let $\breve\xi=(\delta_d-2\delta_u)/(\delta_d-\delta_u)$. Then
--   $$
--   \bar\tau_{\mathsf{IS}}(1)=\frac{\delta_{\mathsf{IS}}}{\delta_{\mathsf{IS}}+\delta_u},\qquad \underline\tau_{\mathsf{IS}}(0)=\frac{\delta_d}{\delta_{\mathsf{IS}}+\delta_d},
--   $$
--   and the hypotheses of Proposition 3,
--   $$
--   \delta_d>2\delta_u\quad\text{and}\quad \delta_{\mathsf{IS}}>\max\Big(\delta_d-2\delta_u,\ \frac{\delta_d\delta_u}{\delta_d-2\delta_u}\Big),
--   $$
--   hold if and only if $\bar\tau_{\mathsf{IS}}(1)>\breve\xi>\underline\tau_{\mathsf{IS}}(0)$.
--
--   The equivalence translates the hypotheses of Proposition 3 and Lemma 2 into an ordering of the three thresholds, which is what makes the three regimes of $\xi$ in those results partition $(0,1)$.
--
--   **Formalization Note** When $\delta_d=2\delta_u$ the quotient $\delta_d\delta_u/(\delta_d-2\delta_u)$ takes Lean's default value $0$, and when $\delta_d=\delta_u$ so does $\breve\xi$; in both corners the left side fails (its first conjunct) and the right side fails as well, so the equivalence holds as stated.
-- source:
--   Candogan, Gurkan, The Value of Information Design in Supply Chain Management, SSRN 4378997 (preprint), p. 32, proof of Lemma 2, display after the K_IS display

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_SCInfoDesign_Intersecting_Setting

namespace SCInfoDesign.Intersecting
theorem hypotheses_equiv (P : Params) (hu : 0 < P.δu) (hd : 0 < P.δd) (hIS : 0 < P.δIS) :
    P.τbarIS 1 = P.δIS / (P.δIS + P.δu) ∧
    P.τlowIS 0 = P.δd / (P.δIS + P.δd) ∧
    ((2 * P.δu < P.δd ∧ max (P.δd - 2 * P.δu) (P.δd * P.δu / (P.δd - 2 * P.δu)) < P.δIS) ↔
      (P.τlowIS 0 < P.ξbreve ∧ P.ξbreve < P.τbarIS 1)) := by sorry
end SCInfoDesign.Intersecting
