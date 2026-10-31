-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P41_hardyBoundaryUniqueness
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P41.hardyBoundaryUniqueness
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:36:36.845788+00:00
-- url     : https://prove2.me/theorems/e29183f8-8e40-4f19-8b7e-87f50d4307f8
-- title:
--   Hardy L² boundary uniqueness
-- statement:
--   Let $N\ge2$, let $\mu$ be normalized angular Haar measure on $\mathbb R/(2\pi\mathbb Z)$, and let $H^2$ be the Hilbert-closed complex span in $L^2(\mu;\mathbb C^N)$ of $\theta\mapsto e^{in\theta}v$, for $n\ge0$ and $v\in\mathbb C^N$. Let $J$ be the image of $(a,b)$ with $0<b-a<2\pi$. For every $F\in H^2$,
--
--   $$F=0\quad\mu\text{-almost everywhere on }J\quad\Longrightarrow\quad F=0\text{ in }L^2(\mu;\mathbb C^N).$$
--
--   This is boundary uniqueness for closed Hardy L² classes, without smoothness or pointwise boundary convergence. The source prints the semicircle-supported case; its local smoothing/reflection argument only requires a smaller subarc of the zero arc. The Hardy-preserving Möbius action on p.11 and interval transport on p.21 give the same localization. This is the requested supporting interface, still a theorem draft with sorry, not a proved downstream resolution.
-- source:
--   Operator Algebras and Conformal Field Theory III. Fusion of positive energy representations of LSU(N) using bounded operators, arXiv:math/9806031v1, PDF p. 20, §14: Suppose that the negative Fourier coefficients

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P41

noncomputable section

open scoped BigOperators

open MeasureTheory Set

namespace QAlgorithms.Papers.Independent.Intakenext100.P41

/-- §14, first proof, PDF p.20: Hardy L² boundary uniqueness.
The printed argument uses a function supported on the upper semicircle. Its
smoothing/reflection argument localizes to a smaller subarc of any zero arc;
§4 p.11 and the interval-transport remark on p.21 give the same localization.
No smoothness or pointwise boundary convergence is imposed on f. -/
theorem hardyBoundaryUniqueness
    (N : ℕ) (hN : 2 ≤ N) (f : CircleL2 N) (hf : f ∈ circleHardySpace N)
    (a b : ℝ) (hab : a < b) (hproper : b - a < 2 * Real.pi)
    (hzero : VanishesOnArc f a b) : f = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P41

end
