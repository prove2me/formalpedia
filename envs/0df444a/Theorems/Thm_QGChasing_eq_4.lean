-- Prove2me | Theorems.Thm_QGChasing_eq_4
-- name    : QGChasing.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:31:13.578523+00:00
-- url     : https://prove2.me/theorems/9ce2337c-ab33-40cf-950f-504fc3875013
-- title:
--   Proof of Theorem 1.1 — the amortized bound (4) for every CPD round
-- statement:
--   Throughout, $\kappa\ge1$, $X\subseteq\mathbb R^d$ is nonempty, closed and convex, the hitting cost $f=f_t$ lies in $\mathcal F_\kappa$, $p=x_{t-1}\in X$ is the previous decision, $v=v_t$ is the global minimizer of $f$, and $g=g_t=f-f(v)$ is the shifted cost. $v^X$ denotes the point of $\arg\min_{z\in X}g(z)$ nearest to $p$, and $r=\frac1{2\kappa^{1/3}}$, $\beta=1+3r$, $C=\frac{32}{7}(1+\kappa^{1/3})$ are the parameters (3).
--
--   Let $x_t$ be the CPD decision of Algorithm 1 from $p$ on $f$. Then for every comparator $u_t\in X$,
--   $$
--   g(x_t)+\|x_t-p\|+C\big(\|x_t-u_t\|-\|p-u_t\|\big)\le C\,g(u_t). \tag{4}
--   $$
--   Summed over rounds with the potential $C\|x_t-u_t\|$, this per-round bound gives Theorem 1.1.
--
--   Differences from the source:
--   - encoding: Π_S, the arg min of line 3, the proximal point (8) and the smallest μ_t, computed by Algorithm 1 → relational predicates: membership in the published nearest-point set SuperPolyak.nearestPoints, IsProxPoint and IsCPDBalanced (minimality of μ_t as a clause); reason: no junk-valued projection or sInf; each predicate has exactly one solution (Lemma 4.1 and cpd_step_exists_unique)
--   - generalization: x_{t−1} is the previous decision of a CPD run → any p ∈ X; reason: the argument uses only x_{t−1} ∈ X; every CPD decision lies in X (cpd_step_exists_unique), so the round of a run is an instance
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), proof of Theorem 1.1, Eq. (4), pp.7–8

import Mathlib
import Definitions.Def_QGChasing_InFkappa
import Definitions.Def_QGChasing_cpdC
import Definitions.Def_QGChasing_IsCPDStep

namespace QGChasing

/-- **Proof of Theorem 1.1, Eq. (4)** (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), pp.7–8). Every CPD round satisfies the amortized
bound
`g_t(x_t) + ‖x_t − x_{t−1}‖ + C(‖x_t − u_t‖ − ‖x_{t−1} − u_t‖) ≤ C g_t(u_t)`
for every comparator `u_t ∈ X`, where `C = (32/7)(1 + κ^{1/3})`.

Here `p = x_{t−1} ∈ X`, `f = f_t ∈ F_κ`, `v = v_t` its global minimizer, `g_t = f − f(v)`, and
`x = x_t` the CPD decision (Algorithm 1, lines 2–7). -/
theorem eq_4 {d : ℕ} (κ : ℝ) (hκ : 1 ≤ κ) (X : Set (EuclideanSpace ℝ (Fin d))) (hXc : IsClosed X) (hXcv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : InFkappa κ f) (p : EuclideanSpace ℝ (Fin d)) (hp : p ∈ X)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ∀ z, f v ≤ f z)
    (x : EuclideanSpace ℝ (Fin d)) (hx : IsCPDStep κ X f p x) (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ X) :
    (f x - f v) + ‖x - p‖ + cpdC κ * (‖x - u‖ - ‖p - u‖) ≤ cpdC κ * (f u - f v) := by sorry

end QGChasing
