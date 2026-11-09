-- Prove2me | Theorems.Thm_ThreeSigma_Upper_lemma_3_2
-- name    : ThreeSigma.Upper.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:56.14304+00:00
-- url     : https://prove2.me/theorems/7f2ca389-5e96-4d32-9dac-dccee5db0b2a
-- title:
--   Lemma 3.2 — nearest-sign rounding
-- statement:
--   Let $A\in[-1,1]^{d\times n}$ and $z\in[-1,1]^n$. Define $x_j=1$ if $z_j\ge0$ and $x_j=-1$ otherwise. With $R(z)=n-\|z\|_2^2$,
--   $$\|Ax\|_\infty\le\|Az\|_\infty+R(z).$$
--   This is the deterministic rounding bound used to pass from a fractional point to a signing.
--
--   Differences from the source:
--   - encoding: vectors in ℝⁿ with coordinates indexed 1 through n → EuclideanSpace ℝ (Fin n) with coordinates indexed 0 through n−1; reason: canonical isometric coordinate representation; no instances are excluded
--   - encoding: the infinity norm of a row vector → the norm on Fin d → ℝ; reason: this is the same finite supremum of absolute coordinates, with norm zero when d=0
-- source:
--   Victor Reis, Zhao Song, Three Standard Deviations Suffice While One Does Not, STOC 2027 submission #393 (October 2026), Lemma 3.2, p. 5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/393.pdf

import Mathlib
import Definitions.Def_ThreeSigma_Upper_Geometry

namespace ThreeSigma.Upper

/-- Lemma 3.2, with the source's deterministic rounding and Pi sup norm on rows. -/
theorem lemma_3_2 {d n : ℕ} (A : Fin d → Fin n → ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) (z : E n) (hz : ∀ j, |z j| ≤ 1) :
    ‖rowProduct A (nearestSign z)‖ ≤ ‖rowProduct A z‖ + R z := by sorry

end ThreeSigma.Upper
