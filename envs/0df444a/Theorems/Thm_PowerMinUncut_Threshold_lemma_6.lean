-- Prove2me | Theorems.Thm_PowerMinUncut_Threshold_lemma_6
-- name    : PowerMinUncut.Threshold.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:43:46.92536+00:00
-- url     : https://prove2.me/theorems/8b863831-a048-43df-84b6-89f0e9626492
-- title:
--   Lemma 6 — ellipse comparison: the normalized chord ratio D_t is dominated by the angular speed P in increasing convex order
-- statement:
--   Let $A$ be an invertible real $2\times2$ matrix and set
--   $$f(\varphi)=\frac{A(\cos\varphi,\sin\varphi)}{\|A(\cos\varphi,\sin\varphi)\|},\quad D_t(\varphi)=\frac{\|f(\varphi+t/2)-f(\varphi-t/2)\|}{2\sin(t/2)},\quad P(\varphi)=\|f'(\varphi)\|.$$
--   For $\varphi$ uniform modulo $2\pi$ and $0<t\le\pi$, $D_t$ is dominated by $P$ in increasing convex order:
--   $$\mathbb E\,\Phi(D_t)\le \mathbb E\,\Phi(P)$$
--   for every finite-valued increasing convex $\Phi:[0,\infty)\to\mathbb R$.
--
--   This deterministic comparison on ellipses is the geometric heart of the global rounding bound (Theorem 7): it controls every chord of a normalized planar image by the derivative.
--
--   Differences from the source:
--   - encoding: uniform φ modulo 2π → (1/2π)∫_0^{2π}; reason: Lean representation of the uniform law on the circle
--   - encoding: Φ : [0, ∞) → ℝ finite-valued increasing convex → Φ : ℝ → ℝ, MonotoneOn and ConvexOn on [0, ∞); reason: D_t and P are nonnegative, so values of Φ on negative reals are never used
--   - encoding: A invertible → A.det ≠ 0; reason: equivalent for square matrices
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), p. 8, Lemma 6

import Mathlib
import Definitions.Def_PowerMinUncut_Threshold_Gaussian

open MeasureTheory ProbabilityTheory Filter Topology

namespace PowerMinUncut.Threshold

/-- **Lemma 6 (ellipse comparison)**, p. 8. For an invertible real `2 × 2` matrix `A`, with
`f(φ) = A(cos φ, sin φ)/‖A(cos φ, sin φ)‖`, `D_t(φ) = ‖f(φ + t/2) - f(φ - t/2)‖/(2 sin(t/2))` and
`P(φ) = ‖f'(φ)‖`, for `φ` uniform modulo `2π` and `0 < t ≤ π`: `EΦ(D_t) ≤ EΦ(P)` for every
finite-valued increasing convex `Φ : [0, ∞) → ℝ`. -/
theorem lemma_6 (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.det ≠ 0) (t : ℝ) (ht : 0 < t)
    (htπ : t ≤ Real.pi) (Φ : ℝ → ℝ) (hΦmono : MonotoneOn Φ (Set.Ici 0))
    (hΦconv : ConvexOn ℝ (Set.Ici 0) Φ) :
    unifAngle (fun φ => Φ (chordRatio A t φ)) ≤ unifAngle (fun φ => Φ (angSpeed A φ)) := by sorry

end PowerMinUncut.Threshold
