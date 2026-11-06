-- Prove2me | Theorems.Thm_QGChasing_lemma_A_2
-- name    : QGChasing.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:25:15.330481+00:00
-- url     : https://prove2.me/theorems/bde91ca7-c0a5-4922-beda-3dc244061603
-- title:
--   Lemma A.2 — $\sqrt{\|y-u\|^2+A^2}-(1-\eta)\|y-u\|+(\gamma-\eta)\|u-v\|\ge\min\{R,A\sqrt{\gamma(2-\gamma)}\}$, Eq. (14)
-- statement:
--   Let $y,u,v\in\mathbb R^d$, $A,R>0$ and $0<\gamma<1$. Set $\eta=\min\{\gamma, R/\|y-v\|\}$, with $\eta=\gamma$ if $y=v$. Then
--   $$
--   \sqrt{\|y-u\|^2+A^2}-(1-\eta)\|y-u\|+(\gamma-\eta)\|u-v\|\ \ge\ \min\big\{R,\ A\sqrt{\gamma(2-\gamma)}\big\}. \tag{14}
--   $$
--   This geometric inequality is the core of Lemma A.1: it bounds the progress of the clipped step toward an arbitrary comparator $u$.
--
--   Differences from the source:
--   - reading: the statement block also contains the line "In particular, ‖u − v‖ ≥ |‖y − v‖ − ‖y − u‖|, 0 < η ≤ γ, η‖y − v‖ = R if η < γ" and, after (14), "And A² = ‖y − p‖² + 2µ(g(y) − g(u)) > 0, R = ‖y − p‖/(2κ^{1/3})" → neither line is a hypothesis or a conclusion; reason: the first lists facts that follow from the setting, the second is the instantiation used in the proof of Lemma A.1 (p.17)
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Lemma A.2, p.17, Eq. (14)

import Mathlib

namespace QGChasing

/-- **Lemma A.2** (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.17, Eq. (14)). Let `y, u, v ∈ ℝᵈ`, `A, R > 0` and `0 < γ < 1`. Set
`η = min{γ, R/‖y − v‖}`, with `η = γ` if `y = v`. Then
`√(‖y − u‖² + A²) − (1 − η)‖y − u‖ + (γ − η)‖u − v‖ ≥ min{R, A√(γ(2 − γ))}`.

**Formalization Note** The page's "In particular …" line lists consequences of the setting and the
"And `A² = …`, `R = …`" line is the instantiation used in the proof of Lemma A.1; neither is a
hypothesis of the lemma. -/
theorem lemma_A_2 {d : ℕ} (y u v : EuclideanSpace ℝ (Fin d)) (A R γ η : ℝ) (hA : 0 < A) (hR : 0 < R)
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hη : η = if y = v then γ else min γ (R / ‖y - v‖)) :
    min R (A * Real.sqrt (γ * (2 - γ))) ≤
      Real.sqrt (‖y - u‖ ^ 2 + A ^ 2) - (1 - η) * ‖y - u‖ + (γ - η) * ‖u - v‖ := by sorry

end QGChasing
