-- Prove2me | Theorems.Thm_RobustDP_ChiSquare_eq50_inner_minimization
-- name    : RobustDP.ChiSquare.eq50_inner_minimization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:11.812026+00:00
-- url     : https://prove2.me/theorems/34c0e623-4904-4fad-9049-81eb55328613
-- title:
--   Proof of Lemma 5, eq. (50) — minimizing the Lagrangian over the ellipsoid
-- statement:
--   Let $\mathcal S$ be a finite set, $q\in\mathcal M(\mathcal S)$ with $q(s)>0$ for every $s$, $t\ge 0$, $v,\mu:\mathcal S\to\mathbb R$ and $\gamma\in\mathbb R$. Over the ellipsoid $E_t=\{y:\sum_s y(s)^2/q(s)\le t\}$,
--
--   $$
--   \min_{y\in E_t}\Big\{\mathbf E^q[v]-\sum_{s}\mu(s)q(s)+\sum_{s}y(s)\big(v(s)-\gamma-\mu(s)\big)\Big\}
--   =\mathbf E^q[v-\mu]-\sqrt{t\sum_{s}q(s)\big(v(s)-\mu(s)-\gamma\big)^2}.
--   $$
--
--   Moreover, put $z(s)=\sqrt{q(s)}\,\big(v(s)-\mu(s)-\gamma\big)$. If $z\ne 0$, the minimum is attained at
--
--   $$
--   y^*(s)=-\frac{\sqrt{t\,q(s)}\,z(s)}{\|z\|},\qquad s\in\mathcal S,
--   $$
--
--   where $\|z\|=\big(\sum_s z(s)^2\big)^{1/2}$: this $y^*$ lies in $E_t$ and achieves the value above.
--
--   This is the inner minimization of the Lagrangian dual of (49), in which the multiplier $\mu\ge 0$ prices the constraint $y\ge -q$ and $\gamma$ prices $\sum_s y(s)=0$. It is the step that turns the χ² ball into a square root of a weighted sum of squares.
--
--   **Formalization Note** The page writes the outer maximum in (50) over $\mu\ge 0,\gamma\ge 0$. Since $\gamma$ is the multiplier of an equality constraint, it ranges over $\mathbb R$ (the proof of Lemma 6 on p. 20 writes $\gamma\in\mathbb R$, and the optimal $\gamma=\mathbf E^q[v-\mu]$ of (51) may be negative); the statement holds for every real $\gamma$ and every $\mu$. The page defines $z$ with $\gamma=\mathbf E^q[v-\mu]$, the optimal $\gamma$ of (51); the attainment clause is stated for every $\gamma$ and contains that case. The "Lagrangian duality" equality between (49) and the outer maximum is Lemma 5 itself and is not posed separately.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), pp. 18–19, proof of Lemma 5, eq. (50) and the attainment sentence after (51)

import Mathlib
import Definitions.Def_RobustDP_ChiSquare_Moments
import Definitions.Def_RobustDP_ChiSquare_ChiSqSet

namespace RobustDP.ChiSquare

/-- Proof of Lemma 5, eq. (50) (Iyengar, TR-2002-07, p. 18): for fixed multipliers `μ` and `γ`
(`γ` real: it is the multiplier of the equality `∑ y = 0`), the inner minimum of the Lagrangian
over the ellipsoid `{y : ∑ y²/q ≤ t}` equals `E^q[v − μ] − √(t ∑ q(s)(v(s) − μ(s) − γ)²)`, and,
when `z(s) = √q(s) (v(s) − μ(s) − γ)` is not zero, it is attained at
`y*(s) = −√(t q(s)) z(s) / ‖z‖`. -/
theorem eq50_inner_minimization {S : Type*} [Fintype S] (q : S → ℝ)
    (hq : q ∈ stdSimplex ℝ S) (hq_pos : ∀ s, 0 < q s) (t : ℝ) (ht : 0 ≤ t)
    (v μ : S → ℝ) (γ : ℝ) :
    IsLeast ((fun y : S → ℝ => expect q v + (-(∑ s, μ s * q s) + ∑ s, y s * (v s - γ - μ s))) ''
        {y : S → ℝ | ∑ s, y s ^ 2 / q s ≤ t})
      (expect q (v - μ) - Real.sqrt (t * ∑ s, q s * (v s - μ s - γ) ^ 2)) ∧
    (0 < ∑ s, q s * (v s - μ s - γ) ^ 2 →
      let z : S → ℝ := fun s => Real.sqrt (q s) * (v s - μ s - γ)
      let ystar : S → ℝ := fun s => -(Real.sqrt (t * q s) * z s) / Real.sqrt (∑ s', z s' ^ 2)
      (∑ s, ystar s ^ 2 / q s ≤ t) ∧
        expect q v + (-(∑ s, μ s * q s) + ∑ s, ystar s * (v s - γ - μ s)) =
          expect q (v - μ) - Real.sqrt (t * ∑ s, q s * (v s - μ s - γ) ^ 2)) := by sorry

end RobustDP.ChiSquare
