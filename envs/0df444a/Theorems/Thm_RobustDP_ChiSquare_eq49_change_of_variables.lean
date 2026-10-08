-- Prove2me | Theorems.Thm_RobustDP_ChiSquare_eq49_change_of_variables
-- name    : RobustDP.ChiSquare.eq49_change_of_variables
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:06.774517+00:00
-- url     : https://prove2.me/theorems/b0a80cee-6c2a-4e1d-bcbd-727d4af36830
-- title:
--   Proof of Lemma 5, eq. (49) — the change of variables $y=p-q$
-- statement:
--   Let $\mathcal S$ be a finite set, $q\in\mathcal M(\mathcal S)$ a probability measure with $q(s)>0$ for every $s$, $t\in\mathbb R$, and $v:\mathcal S\to\mathbb R$. Let $\mathcal P$ be the χ² set (46). Then:
--
--   1. a vector $p$ lies in $\mathcal P$ if and only if $y=p-q$ satisfies
--   $$
--   \sum_{s}\frac{y(s)^2}{q(s)}\le t,\qquad \sum_s y(s)=0,\qquad y\ge -q;
--   $$
--   2. for every real number $V$, $V$ is the minimum of $\mathbf E^p[v]$ over $p\in\mathcal P$ if and only if $V-\mathbf E^q[v]$ is the minimum of
--   $$
--   \sum_s y(s)\,v(s)\quad\text{subject to}\quad \sum_s\frac{y(s)^2}{q(s)}\le t,\ \ \sum_s y(s)=0,\ \ y\ge -q .
--   $$
--
--   In words, the value of the worst-case problem (47) is $\mathbf E^q[v]$ plus the value of problem (49). This is the first step of the proof of Lemma 5: it moves the centre of the ball to the origin, so that the constraints become a centred ellipsoid and two linear constraints.
--
--   **Formalization Note** "Minimum" is Mathlib's `IsLeast` of the image set; the statement says nothing about existence, which is part of Lemma 5 itself.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 18, proof of Lemma 5, eq. (49)

import Mathlib
import Definitions.Def_RobustDP_ChiSquare_Moments
import Definitions.Def_RobustDP_ChiSquare_ChiSqSet

namespace RobustDP.ChiSquare

/-- Proof of Lemma 5, eq. (49) (Iyengar, TR-2002-07, p. 18): with `y = p − q`, `p ∈ P` iff
`∑ y²/q ≤ t`, `∑ y = 0` and `y ≥ −q`; hence the minimum of (47) is `E^q[v]` plus the minimum
of `∑ y(s) v(s)` over those `y`. -/
theorem eq49_change_of_variables {S : Type*} [Fintype S] (q : S → ℝ)
    (hq : q ∈ stdSimplex ℝ S) (hq_pos : ∀ s, 0 < q s) (t : ℝ) (v : S → ℝ) :
    (∀ p : S → ℝ, p ∈ chiSqSet q t ↔
      ((∑ s, (p s - q s) ^ 2 / q s ≤ t) ∧ (∑ s, (p s - q s) = 0) ∧ ∀ s, -q s ≤ p s - q s)) ∧
    ∀ val : ℝ,
      IsLeast ((fun p => expect p v) '' chiSqSet q t) val ↔
        IsLeast ((fun y : S → ℝ => ∑ s, y s * v s) ''
            {y : S → ℝ | (∑ s, y s ^ 2 / q s ≤ t) ∧ (∑ s, y s = 0) ∧ ∀ s, -q s ≤ y s})
          (val - expect q v) := by sorry

end RobustDP.ChiSquare
