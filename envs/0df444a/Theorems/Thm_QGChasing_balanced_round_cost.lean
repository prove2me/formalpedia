-- Prove2me | Theorems.Thm_QGChasing_balanced_round_cost
-- name    : QGChasing.balanced_round_cost
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:14.380526+00:00
-- url     : https://prove2.me/theorems/3c0c440c-66de-42b1-858e-269698d371d7
-- title:
--   Proof of Theorem 1.1 — cost of a balanced round: $g_t(x_t)+\|x_t-x_{t-1}\|\le(2+4r)\|y_t-x_{t-1}\|$
-- statement:
--   Throughout, $\kappa\ge1$, $X\subseteq\mathbb R^d$ is nonempty, closed and convex, the hitting cost $f=f_t$ lies in $\mathcal F_\kappa$, $p=x_{t-1}\in X$ is the previous decision, $v=v_t$ is the global minimizer of $f$, and $g=g_t=f-f(v)$ is the shifted cost. $v^X$ denotes the point of $\arg\min_{z\in X}g(z)$ nearest to $p$, and $r=\frac1{2\kappa^{1/3}}$, $\beta=1+3r$, $C=\frac{32}{7}(1+\kappa^{1/3})$ are the parameters (3).
--
--   Suppose the condition in line 4 of Algorithm 1 is false, and let $(\mu_t,y_t,x_t)$ be the balanced step of line 7. Then
--   $$
--   g(x_t)+\|x_t-p\|\le(2+4r)\,\|y_t-p\|=C\,\frac{7}{16\kappa^{1/3}}\,\|y_t-p\| .
--   $$
--   Both the inequality and the identity are part of the statement. Combined with Lemma 4.2, this gives (4) in the balanced case.
--
--   Differences from the source:
--   - encoding: Π_S, the arg min of line 3, the proximal point (8) and the smallest μ_t, computed by Algorithm 1 → relational predicates: membership in the published nearest-point set SuperPolyak.nearestPoints, IsProxPoint and IsCPDBalanced (minimality of μ_t as a clause); reason: no junk-valued projection or sInf; each predicate has exactly one solution (Lemma 4.1 and cpd_step_exists_unique)
--   - generalization: x_{t−1} is the previous decision of a CPD run → any p ∈ X; reason: the argument uses only x_{t−1} ∈ X; every CPD decision lies in X (cpd_step_exists_unique), so the round of a run is an instance
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), proof of Theorem 1.1, the cost of the second case, p.8

import Mathlib
import Definitions.Def_QGChasing_InFkappa
import Definitions.Def_SuperPolyak_solutionSet
import Definitions.Def_QGChasing_cpdR
import Definitions.Def_QGChasing_cpdBeta
import Definitions.Def_QGChasing_cpdC
import Definitions.Def_QGChasing_IsCPDBalanced

namespace QGChasing

/-- **Proof of Theorem 1.1, cost of a balanced round** (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.8). Suppose the condition in
line 4 of Algorithm 1 is false. Then the decision `x_t` of line 7 satisfies
`g_t(x_t) + ‖x_t − x_{t−1}‖ ≤ (2 + 4r)‖y_t − x_{t−1}‖ = C · 7/(16κ^{1/3}) · ‖y_t − x_{t−1}‖`.

Here `p = x_{t−1} ∈ X`, `f = f_t ∈ F_κ`, `v = v_t` its global minimizer, `g_t = f − f(v)`, `v^X`
the nearest point to `p` of `argmin_X g_t`, and `(μ_t, y_t, x_t)` the balanced step. -/
theorem balanced_round_cost {d : ℕ} (κ : ℝ) (hκ : 1 ≤ κ) (X : Set (EuclideanSpace ℝ (Fin d))) (hXc : IsClosed X) (hXcv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : InFkappa κ f) (p : EuclideanSpace ℝ (Fin d)) (hp : p ∈ X)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ∀ z, f v ≤ f z) (vX : EuclideanSpace ℝ (Fin d))
    (hvX : vX ∈ SuperPolyak.nearestPoints {z | z ∈ X ∧ ∀ w ∈ X, f z - f v ≤ f w - f v} p)
    (htest : f vX - f v < cpdBeta κ * ‖vX - p‖)
    (μ : ℝ) (y x : EuclideanSpace ℝ (Fin d)) (hbal : IsCPDBalanced κ X f p v μ y x) :
    (f x - f v) + ‖x - p‖ ≤ (2 + 4 * cpdR κ) * ‖y - p‖ ∧
      (2 + 4 * cpdR κ) * ‖y - p‖ = cpdC κ * (7 / (16 * κ ^ (1 / 3 : ℝ))) * ‖y - p‖ := by sorry

end QGChasing
