-- Prove2me | Theorems.Thm_ThreeSigma_Upper_lemma_3_3
-- name    : ThreeSigma.Upper.lemma_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:57.510349+00:00
-- url     : https://prove2.me/theorems/1fa24b53-3070-48f3-b13e-ee95a687913b
-- title:
--   Lemma 3.3 — scalar estimates (all parts)
-- statement:
--   Let $\phi(t)=5/\sinh(t^2/3)$, $\psi(t)=-t\phi'(t)-2\phi(t)$, and $c=\sqrt{3\operatorname{arsinh}(10)}$. All four conclusions hold:
--
--   1. For every $t>0$,
--   $$\phi(t)>0,\quad\phi'(t)<0,\quad\phi''(t)>0;\qquad \phi(c)=\frac12,\quad\lim_{t\downarrow0}\phi(t)=+\infty.$$
--   2. For every $t>0$,
--   $$\psi(t)>0.$$
--   3. For every $t,\theta>0$,
--   $$\min\{\phi''(t),\theta\}\le\frac34\psi(t)+\frac14\theta\phi(t).$$
--   4. For every fixed $\Delta>0$, the function
--   $$s\longmapsto s^{-1}\phi(\Delta/\sqrt{s})$$
--   is strictly increasing on $(0,\infty)$.
--
--   These are the complete scalar estimates used in the upper bound.
--
--   Differences from the source:
--   - encoding: φ is extended-valued with φ(0)=+∞ → the real formula phi(t)=5/sinh(t²/3), whose value at zero is 0; reason: all scalar assertions and derivative evaluations use strictly positive arguments or the right limit; the extensions agree on a neighborhood of each such point
-- source:
--   Victor Reis, Zhao Song, Three Standard Deviations Suffice While One Does Not, STOC 2027 submission #393 (October 2026), Lemma 3.3(a)–(d), p. 6; proofs in Appendix C, pp. 14–15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/393.pdf

import Mathlib
import Definitions.Def_ThreeSigma_Upper_Scalar

namespace ThreeSigma.Upper

/-- Lemma 3.3(a)-(d), including the value at c, the right limit at zero,
and strict monotonicity on the entire positive half-line. -/
theorem lemma_3_3 :
    ((∀ t : ℝ, 0 < t → 0 < phi t ∧ deriv phi t < 0 ∧ 0 < deriv (deriv phi) t) ∧
      phi c = (1 / 2 : ℝ) ∧
      Filter.Tendsto phi (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop) ∧
    (∀ t : ℝ, 0 < t → 0 < psi t) ∧
    (∀ t θ : ℝ, 0 < t → 0 < θ →
      min (deriv (deriv phi) t) θ ≤ (3 / 4 : ℝ) * psi t + (1 / 4 : ℝ) * θ * phi t) ∧
    (∀ Δ : ℝ, 0 < Δ →
      StrictMonoOn (fun u : ℝ => u⁻¹ * phi (Δ / Real.sqrt u)) (Set.Ioi 0)) := by sorry

end ThreeSigma.Upper
