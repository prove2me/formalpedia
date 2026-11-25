-- Prove2me | Theorems.Thm_SSLWithoutPairs_exact_integral
-- name    : SSLWithoutPairs.exact_integral
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T06:41:27.177858+00:00
-- url     : https://prove2.me/theorems/355c2b4f-78fd-4170-92c4-618d2e89d795
-- title:
--   Eq. (14): exact integral of the decoupled dynamics (as proved)
-- statement:
--   Let $\alpha_p>0$, $\eta\ge0$, and let $\tau(t)$ be any real function. If $p_j(t),s_j(t)$, $t\ge0$, solve
--
--   $$\dot p_j=\alpha_ps_j[\tau-(1+\sigma^2)p_j]-\eta p_j,\qquad \dot s_j=2p_js_j[\tau-(1+\sigma^2)p_j]-2\eta s_j,$$
--
--   then for all $t\ge0$
--
--   $$s_j(t)=\alpha_p^{-1}p_j^2(t)+e^{-2\eta t}c_j,\qquad c_j=s_j(0)-\alpha_p^{-1}p_j^2(0).$$
--
--   With weight decay the trajectory approaches the invariant parabola $s_j=\alpha_p^{-1}p_j^2$.
--
--   **Formalization Note** The paper prints $c_j=\alpha_p^{-1}p_j^2(0)-s_j(0)$. Setting $t=0$ in the identity forces the sign used here, which is also what the derivation in Appendix B.1 gives.
-- source:
--   Tian, Chen and Ganguli, Understanding Self-Supervised Learning Dynamics without Contrastive Pairs, arXiv:2102.06810v4 (2021), Section 3.2, eq. (14), p. 5; derivation in Appendix B.1, eqs. (79)-(86), p. 18

import Mathlib
import Definitions.Def_SSLWithoutPairs_Basic

open MeasureTheory ProbabilityTheory Filter Topology Matrix

namespace SSLWithoutPairs

theorem exact_integral (αp σ η : ℝ) (hαp : 0 < αp) (hη : 0 ≤ η) (τ p s : ℝ → ℝ)
    (hp : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt p (modeFlowP αp σ η (τ t) (p t) (s t)) (Set.Ici 0) t)
    (hs : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt s (modeFlowS σ η (τ t) (p t) (s t)) (Set.Ici 0) t) :
    ∀ t : ℝ, 0 ≤ t →
      s t = αp⁻¹ * p t ^ 2 + Real.exp (-2 * η * t) * (s 0 - αp⁻¹ * p 0 ^ 2) := by sorry

end SSLWithoutPairs
