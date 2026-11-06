-- Prove2me | Theorems.Thm_QGChasing_lemma_A_1
-- name    : QGChasing.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:25:24.678842+00:00
-- url     : https://prove2.me/theorems/9d78c57c-5773-4053-a2d9-ff74299e006e
-- title:
--   Lemma A.1 — progress of the projected clipped step, Eq. (12)
-- statement:
--   Let $p,y,u,v\in\mathbb R^d$ with $p\ne y$ and $y\ne v$, let $\mu,\lambda>0$, $\kappa\ge1$ and $0<\gamma<1$, and let $g:\mathbb R^d\to\mathbb R$. Suppose that
--   $$
--   0\le g(u)\le g(y),\qquad g(u)\ge\frac{\lambda}{2}\|u-v\|^2,\qquad \|p-u\|^2\ge\|y-u\|^2+\|y-p\|^2+2\mu\big(g(y)-g(u)\big).
--   $$
--   Let $S$ be a closed convex set containing $y$ and $u$, and set
--   $$
--   \eta=\min\Big\{\gamma,\ \frac{\|y-p\|}{2\kappa^{1/3}\|y-v\|}\Big\},\qquad x=\Pi_S\big\{(1-\eta)y+\eta v\big\}.
--   $$
--   Then
--   $$
--   \|p-u\|-\|x-u\|+g(u)\ \ge\ \min\Big\{\frac{\|y-p\|}{2\kappa^{1/3}},\ \sqrt{\gamma(2-\gamma)\big(\|y-p\|^2+2\mu(g(y)-g(u))\big)}\Big\}+g(u)-\gamma\sqrt{\frac{2g(u)}{\lambda}} . \tag{12}
--   $$
--   The display (13) on p.15 repeats (12) verbatim. In the proof of Lemma 4.2 the lemma is applied with $S=X\cap\{z:g(z)\le g(y_t)\}$.
--
--   Differences from the source:
--   - generalization: g is the shifted cost g_t of the proof of Lemma 4.2 → g is any function ℝᵈ → ℝ; reason: the lemma's hypotheses and conclusion involve only g(u) and g(y); g_t is one such function
--   - encoding: conclusions (12) and (13), printed identically → one conclusion; reason: (13) repeats (12) character for character
--   - encoding: x = Π_S{(1 − η)y + ηv}, the Euclidean projection onto S → x ∈ SuperPolyak.nearestPoints S ((1 − η)y + ηv) and η a variable with η = min{…} as a hypothesis; reason: S is nonempty (y ∈ S), closed and convex, so the nearest point exists and is unique and the relation picks exactly Π_S
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Lemma A.1, pp.14–15 (statement p.14, conclusion (12) p.15)

import Mathlib
import Definitions.Def_SuperPolyak_solutionSet

namespace QGChasing

/-- **Lemma A.1** (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), pp.14–15, Eq. (12); (13) repeats (12)). Let `p, y, u, v ∈ ℝᵈ`, `p ≠ y`,
`y ≠ v`, `μ, λ > 0`, `κ ≥ 1` and `0 < γ < 1`. Suppose that `0 ≤ g(u) ≤ g(y)`,
`g(u) ≥ (λ/2)‖u − v‖²` and `‖p − u‖² ≥ ‖y − u‖² + ‖y − p‖² + 2μ(g(y) − g(u))`. Let `S` be a
closed convex set containing `y` and `u`, and set `η = min{γ, ‖y − p‖/(2κ^{1/3}‖y − v‖)}`,
`x = Π_S{(1 − η)y + ηv}`. Then
`‖p − u‖ − ‖x − u‖ + g(u) ≥ min{‖y − p‖/(2κ^{1/3}), √(γ(2 − γ)(‖y − p‖² + 2μ(g(y) − g(u))))} + g(u) − γ√(2g(u)/λ)`.

**Formalization Note** `g` is any real function on `ℝᵈ` (only `g(u)` and `g(y)` occur); `λ` is
named `lam`; the projection is relational (membership in the published nearest-point set `SuperPolyak.nearestPoints`). -/
theorem lemma_A_1 {d : ℕ} (p y u v : EuclideanSpace ℝ (Fin d)) (hpy : p ≠ y) (hyv : y ≠ v)
    (μ lam κ γ : ℝ) (hμ : 0 < μ) (hlam : 0 < lam) (hκ : 1 ≤ κ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (g : EuclideanSpace ℝ (Fin d) → ℝ) (hgu0 : 0 ≤ g u) (hguy : g u ≤ g y) (hqg : lam / 2 * ‖u - v‖ ^ 2 ≤ g u)
    (hpu : ‖y - u‖ ^ 2 + ‖y - p‖ ^ 2 + 2 * μ * (g y - g u) ≤ ‖p - u‖ ^ 2)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hSc : IsClosed S) (hScv : Convex ℝ S) (hyS : y ∈ S) (huS : u ∈ S)
    (η : ℝ) (hη : η = min γ (‖y - p‖ / (2 * κ ^ (1 / 3 : ℝ) * ‖y - v‖)))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ SuperPolyak.nearestPoints S ((1 - η) • y + η • v)) :
    min (‖y - p‖ / (2 * κ ^ (1 / 3 : ℝ)))
        (Real.sqrt (γ * (2 - γ) * (‖y - p‖ ^ 2 + 2 * μ * (g y - g u)))) +
      g u - γ * Real.sqrt (2 * g u / lam) ≤
      ‖p - u‖ - ‖x - u‖ + g u := by sorry

end QGChasing
