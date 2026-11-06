-- Prove2me | Theorems.Thm_QGChasing_lemma_4_1
-- name    : QGChasing.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:15.027087+00:00
-- url     : https://prove2.me/theorems/c1e2ff1f-551c-48c2-989e-7e8216bf0d52
-- title:
--   Lemma 4.1 — the smallest balancing parameter exists, $s_t>0$, $y_t\ne v_t$, $0<\eta_t\le\gamma_t<r^2\le\frac14$
-- statement:
--   Throughout, $\kappa\ge1$, $X\subseteq\mathbb R^d$ is nonempty, closed and convex, the hitting cost $f=f_t$ lies in $\mathcal F_\kappa$, $p=x_{t-1}\in X$ is the previous decision, $v=v_t$ is the global minimizer of $f$, and $g=g_t=f-f(v)$ is the shifted cost. $v^X$ denotes the point of $\arg\min_{z\in X}g(z)$ nearest to $p$, and $r=\frac1{2\kappa^{1/3}}$, $\beta=1+3r$, $C=\frac{32}{7}(1+\kappa^{1/3})$ are the parameters (3).
--
--   Suppose we are in the case of line 7 of Algorithm 1, that is, $g(v^X)<\beta\|v^X-p\|$. Then
--
--   1. the smallest positive balancing parameter $\mu_t$ exists, together with its proximal point $y_t=y_t(\mu_t)$ and the final projection $x_t$ of line 7;
--   2. for every such balanced step $(\mu_t,y_t,x_t)$, with $s_t=\|y_t-p\|$, $\gamma_t=\frac{r^2s_t}{s_t+\beta\mu_t}$ and $\eta_t=\min\{\gamma_t, rs_t/\|y_t-v\|\}$:
--   $$
--   s_t>0,\qquad g(y_t)=\beta s_t>0,\qquad y_t\ne v,\qquad 0<\eta_t\le\gamma_t<r^2\le\tfrac14 .
--   $$
--
--   The lemma shows that line 7 is well defined and that the clipped fraction is a genuine, small step.
--
--   Differences from the source:
--   - encoding: Π_S, the arg min of line 3, the proximal point (8) and the smallest μ_t, computed by Algorithm 1 → relational predicates: membership in the published nearest-point set SuperPolyak.nearestPoints, IsProxPoint and IsCPDBalanced (minimality of μ_t as a clause); reason: no junk-valued projection or sInf; each predicate has exactly one solution (Lemma 4.1 and cpd_step_exists_unique)
--   - generalization: x_{t−1} is the previous decision of a CPD run → any p ∈ X; reason: the argument uses only x_{t−1} ∈ X; every CPD decision lies in X (cpd_step_exists_unique), so the round of a run is an instance
--   - generalization: the smallest μ_t exists → the whole balanced step (μ_t, y_t, x_t) exists, including the final projection; reason: the existence of the projection is the last sentence of the proof (p.14); dropping x gives the printed clause
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), Lemma 4.1, p.6; proof pp.12–14

import Mathlib
import Definitions.Def_QGChasing_InFkappa
import Definitions.Def_SuperPolyak_solutionSet
import Definitions.Def_QGChasing_cpdR
import Definitions.Def_QGChasing_cpdBeta
import Definitions.Def_QGChasing_cpdGamma
import Definitions.Def_QGChasing_cpdEta
import Definitions.Def_QGChasing_IsCPDBalanced

namespace QGChasing

/-- **Lemma 4.1** (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.6; proof pp.12–14). In the case of line 7 of Algorithm 1 (the line-4
test fails: `g(v^X) < β‖v^X − x_{t−1}‖`), the smallest positive balancing parameter `μ_t` exists
(together with its proximal point `y_t` and the final projection `x_t`), and for every such
`(μ_t, y_t, x_t)`: `s_t > 0`, `g_t(y_t) = βs_t > 0`, `y_t ≠ v_t` and
`0 < η_t ≤ γ_t < r² ≤ 1/4`.

Here `p = x_{t−1} ∈ X`, `f = f_t ∈ F_κ`, `v = v_t` its global minimizer, `g_t = f − f(v)`, and
`v^X` the nearest point to `p` of `argmin_X g_t`.

**Formalization Note** The existence part is `∃ μ y x, IsCPDBalanced …`; it includes the existence
of the final projection, which the proof establishes in its last sentence (p.14). -/
theorem lemma_4_1 {d : ℕ} (κ : ℝ) (hκ : 1 ≤ κ) (X : Set (EuclideanSpace ℝ (Fin d))) (hXc : IsClosed X) (hXcv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : InFkappa κ f) (p : EuclideanSpace ℝ (Fin d)) (hp : p ∈ X)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ∀ z, f v ≤ f z) (vX : EuclideanSpace ℝ (Fin d))
    (hvX : vX ∈ SuperPolyak.nearestPoints {z | z ∈ X ∧ ∀ w ∈ X, f z - f v ≤ f w - f v} p)
    (htest : f vX - f v < cpdBeta κ * ‖vX - p‖) :
    (∃ (μ : ℝ) (y x : EuclideanSpace ℝ (Fin d)), IsCPDBalanced κ X f p v μ y x) ∧
    ∀ (μ : ℝ) (y x : EuclideanSpace ℝ (Fin d)), IsCPDBalanced κ X f p v μ y x →
      0 < ‖y - p‖ ∧ f y - f v = cpdBeta κ * ‖y - p‖ ∧ 0 < cpdBeta κ * ‖y - p‖ ∧ y ≠ v ∧
      0 < cpdEta κ ‖y - p‖ μ ‖y - v‖ ∧ cpdEta κ ‖y - p‖ μ ‖y - v‖ ≤ cpdGamma κ ‖y - p‖ μ ∧
      cpdGamma κ ‖y - p‖ μ < cpdR κ ^ 2 ∧ cpdR κ ^ 2 ≤ 1 / 4 := by sorry

end QGChasing
