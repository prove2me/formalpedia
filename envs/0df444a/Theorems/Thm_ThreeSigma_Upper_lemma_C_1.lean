-- Prove2me | Theorems.Thm_ThreeSigma_Upper_lemma_C_1
-- name    : ThreeSigma.Upper.lemma_C_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:53.543206+00:00
-- url     : https://prove2.me/theorems/524783d2-7a4c-43c1-839c-767d2fce9a88
-- title:
--   Lemma C.1 — scalar comparison
-- statement:
--   For every positive real $t$, with $\phi(t)=5/\sinh(t^2/3)$ and $\psi(t)=-t\phi'(t)-2\phi(t)$,
--   $$\left(1-\frac{\phi(t)}4\right)\phi''(t)\le\frac34\psi(t).$$
--   The derivatives are those of the explicit scalar function. This is the scalar comparison used in Lemma 3.3(c).
--
--   Differences from the source:
--   - encoding: φ is extended-valued with φ(0)=+∞ → the real formula phi(t)=5/sinh(t²/3), whose value at zero is 0; reason: all scalar assertions and derivative evaluations use strictly positive arguments or the right limit; the extensions agree on a neighborhood of each such point
-- source:
--   Victor Reis, Zhao Song, Three Standard Deviations Suffice While One Does Not, STOC 2027 submission #393 (October 2026), Lemma C.1, p. 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/393.pdf

import Mathlib
import Definitions.Def_ThreeSigma_Upper_Scalar

namespace ThreeSigma.Upper

/-- Lemma C.1 (p. 14), about the actual second derivative of φ. -/
theorem lemma_C_1 (t : ℝ) (ht : 0 < t) :
    (1 - phi t / 4) * deriv (deriv phi) t ≤ (3 / 4 : ℝ) * psi t := by sorry

end ThreeSigma.Upper
