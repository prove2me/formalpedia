-- Prove2me | Theorems.Thm_QGChasing_lemma_4_2
-- name    : QGChasing.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:23.795247+00:00
-- url     : https://prove2.me/theorems/c561d934-ce18-4089-a8ad-2beed7cb11e2
-- title:
--   Lemma 4.2 — $\|x_{t-1}-u_t\|-\|x_t-u_t\|+g_t(u_t)\ge\frac{7}{16\kappa^{1/3}}\|y_t-x_{t-1}\|$
-- statement:
--   Throughout, $\kappa\ge1$, $X\subseteq\mathbb R^d$ is nonempty, closed and convex, the hitting cost $f=f_t$ lies in $\mathcal F_\kappa$, $p=x_{t-1}\in X$ is the previous decision, $v=v_t$ is the global minimizer of $f$, and $g=g_t=f-f(v)$ is the shifted cost. $v^X$ denotes the point of $\arg\min_{z\in X}g(z)$ nearest to $p$, and $r=\frac1{2\kappa^{1/3}}$, $\beta=1+3r$, $C=\frac{32}{7}(1+\kappa^{1/3})$ are the parameters (3).
--
--   Suppose the condition in line 4 of Algorithm 1 is false, and let $(\mu_t,y_t,x_t)$ be the balanced step of line 7. Then every $u_t\in X$ satisfies
--   $$
--   \|p-u_t\|-\|x_t-u_t\|+g(u_t)\ \ge\ \frac{7}{16\kappa^{1/3}}\,\|y_t-p\| .
--   $$
--   The left side is the decrease of the potential $\|x-u_t\|$ plus the comparator's shifted hitting cost; the lemma says it pays for a fixed fraction of the proximal step. With the cost bound of a balanced round it gives (4) in the second case.
--
--   Differences from the source:
--   - encoding: Π_S, the arg min of line 3, the proximal point (8) and the smallest μ_t, computed by Algorithm 1 → relational predicates: membership in the published nearest-point set SuperPolyak.nearestPoints, IsProxPoint and IsCPDBalanced (minimality of μ_t as a clause); reason: no junk-valued projection or sInf; each predicate has exactly one solution (Lemma 4.1 and cpd_step_exists_unique)
--   - generalization: x_{t−1} is the previous decision of a CPD run → any p ∈ X; reason: the argument uses only x_{t−1} ∈ X; every CPD decision lies in X (cpd_step_exists_unique), so the round of a run is an instance
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Lemma 4.2, p.8; proof pp.14–16

import Mathlib
import Definitions.Def_QGChasing_InFkappa
import Definitions.Def_SuperPolyak_solutionSet
import Definitions.Def_QGChasing_cpdBeta
import Definitions.Def_QGChasing_IsCPDBalanced

namespace QGChasing

/-- **Lemma 4.2** (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.8; proof pp.14–16). Suppose that the condition in line 4 of
Algorithm 1 is false. Then every `u_t ∈ X` satisfies
`‖x_{t−1} − u_t‖ − ‖x_t − u_t‖ + g_t(u_t) ≥ 7/(16κ^{1/3}) ‖y_t − x_{t−1}‖`.

Here `p = x_{t−1} ∈ X`, `f = f_t ∈ F_κ`, `v = v_t` its global minimizer, `g_t = f − f(v)`, `v^X`
the nearest point to `p` of `argmin_X g_t`, and `(μ_t, y_t, x_t)` the balanced step of line 7. -/
theorem lemma_4_2 {d : ℕ} (κ : ℝ) (hκ : 1 ≤ κ) (X : Set (EuclideanSpace ℝ (Fin d))) (hXc : IsClosed X) (hXcv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : InFkappa κ f) (p : EuclideanSpace ℝ (Fin d)) (hp : p ∈ X)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ∀ z, f v ≤ f z) (vX : EuclideanSpace ℝ (Fin d))
    (hvX : vX ∈ SuperPolyak.nearestPoints {z | z ∈ X ∧ ∀ w ∈ X, f z - f v ≤ f w - f v} p)
    (htest : f vX - f v < cpdBeta κ * ‖vX - p‖)
    (μ : ℝ) (y x : EuclideanSpace ℝ (Fin d)) (hbal : IsCPDBalanced κ X f p v μ y x) (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ X) :
    7 / (16 * κ ^ (1 / 3 : ℝ)) * ‖y - p‖ ≤ ‖p - u‖ - ‖x - u‖ + (f u - f v) := by sorry

end QGChasing
