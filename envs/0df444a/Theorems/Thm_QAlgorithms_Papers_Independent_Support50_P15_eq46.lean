-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_eq46
-- name    : QAlgorithms.Papers.Independent.Support50.P15.eq46
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:48:11.713202+00:00
-- url     : https://prove2.me/theorems/2d4faaa6-bb40-40a6-808d-f42cb4ca3225
-- title:
--   eq46
-- statement:
--   Let $\rho,\sigma$ be normalized states in dimension $d\ge2$ and let the coding base $D>1$ be real. Define expected savings $\delta=(S(\rho)-S(\sigma))/\log D$. With relative entropy in nats and infinity retained,
--
--   $$\frac{D(\rho\|\sigma)}{\log D}\ge\frac{M(\delta\log D,d)}{\log D}.$$
--
--   If $\delta\ge0$, the latter quantity is at least $2\delta^2\log D/(\log^2(d-1)+4)$. The entropic inequality holds for classical diagonal laws and quantum states; an actual code alphabet has integer size at least two. It bounds the excess length arising from a wrong source model.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 14, eq46

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Eq. (46), PDF pp.14--15, valid for both classical and quantum states.
Only the final quadratic bound requires nonnegative savings. -/
theorem eq46 {d : ℕ} (hd : 2 ≤ d) (a b : EntropyState d) (base : ℝ) (hb : 1 < base) :
    let delta := difference a.val b.val / Real.log base
    tightBound d (delta * Real.log base) / (Real.log base : EReal) ≤ stateRelativeNats a b / (Real.log base : EReal) ∧
    (0 ≤ delta → ((delta ^ 2 * (2 * Real.log base) / redundancyScale d : ℝ) : EReal) ≤
      tightBound d (delta * Real.log base) / (Real.log base : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
