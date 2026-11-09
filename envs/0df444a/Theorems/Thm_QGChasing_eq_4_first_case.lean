-- Prove2me | Theorems.Thm_QGChasing_eq_4_first_case
-- name    : QGChasing.eq_4_first_case
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T02:26:39.789204+00:00
-- url     : https://prove2.me/theorems/8ad2d167-d9af-413e-bdd2-9fec1588619c
-- title:
--   Proof of Theorem 1.1 — Eq. (4) when the line-4 test holds
-- statement:
--   Throughout, $\kappa\ge1$, $X\subseteq\mathbb R^d$ is nonempty, closed and convex, the hitting cost $f=f_t$ lies in $\mathcal F_\kappa$, $p=x_{t-1}\in X$ is the previous decision, $v=v_t$ is the global minimizer of $f$, and $g=g_t=f-f(v)$ is the shifted cost. $v^X$ denotes the point of $\arg\min_{z\in X}g(z)$ nearest to $p$, and $r=\frac1{2\kappa^{1/3}}$, $\beta=1+3r$, $C=\frac{32}{7}(1+\kappa^{1/3})$ are the parameters (3).
--
--   Suppose the condition in line 4 of Algorithm 1 holds, $g(v^X)\ge\beta\|v^X-p\|$, so that $x_t=v^X$. Then for every comparator $u_t\in X$ the amortized bound (4) holds:
--   $$
--   g(x_t)+\|x_t-p\|+C\big(\|x_t-u_t\|-\|p-u_t\|\big)\le C\,g(u_t).
--   $$
--
--   Differences from the source:
--   - encoding: Π_S, the arg min of line 3, the proximal point (8) and the smallest μ_t, computed by Algorithm 1 → relational predicates: membership in the published nearest-point set SuperPolyak.nearestPoints, IsProxPoint and IsCPDBalanced (minimality of μ_t as a clause); reason: no junk-valued projection or sInf; each predicate has exactly one solution (Lemma 4.1 and cpd_step_exists_unique)
--   - generalization: x_{t−1} is the previous decision of a CPD run → any p ∈ X; reason: the argument uses only x_{t−1} ∈ X; every CPD decision lies in X (cpd_step_exists_unique), so the round of a run is an instance
--   - encoding: x_t = v^X_t → the statement written with vX in place of x_t; reason: line 5 sets x_t = v^X_t
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), proof of Theorem 1.1, Eq. (4), first case, p.7

import Mathlib
import Definitions.Def_QGChasing_InFkappa
import Definitions.Def_SuperPolyak_solutionSet
import Definitions.Def_QGChasing_cpdBeta
import Definitions.Def_QGChasing_cpdC

namespace QGChasing

/-- **Proof of Theorem 1.1, Eq. (4) in the first case** (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.7). If the condition in line 4
of Algorithm 1 holds, `g(v^X) ≥ β‖v^X − x_{t−1}‖`, then `x_t = v^X` satisfies the amortized bound
(4) for every comparator `u_t ∈ X`:
`g_t(x_t) + ‖x_t − x_{t−1}‖ + C(‖x_t − u_t‖ − ‖x_{t−1} − u_t‖) ≤ C g_t(u_t)`.

Here `p = x_{t−1} ∈ X`, `f = f_t ∈ F_κ`, `v = v_t` its global minimizer, `g_t = f − f(v)`, `v^X`
the nearest point to `p` of `argmin_X g_t`, and `C = (32/7)(1 + κ^{1/3})`. -/
theorem eq_4_first_case {d : ℕ} (κ : ℝ) (hκ : 1 ≤ κ) (X : Set (EuclideanSpace ℝ (Fin d))) (hXc : IsClosed X) (hXcv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : InFkappa κ f) (p : EuclideanSpace ℝ (Fin d)) (hp : p ∈ X)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ∀ z, f v ≤ f z) (vX : EuclideanSpace ℝ (Fin d))
    (hvX : vX ∈ SuperPolyak.nearestPoints {z | z ∈ X ∧ ∀ w ∈ X, f z - f v ≤ f w - f v} p)
    (htest : cpdBeta κ * ‖vX - p‖ ≤ f vX - f v) (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ X) :
    (f vX - f v) + ‖vX - p‖ + cpdC κ * (‖vX - u‖ - ‖p - u‖) ≤ cpdC κ * (f u - f v) := by sorry

end QGChasing
