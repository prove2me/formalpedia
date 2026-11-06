-- Prove2me | Theorems.Thm_QGChasing_cpd_step_exists_unique
-- name    : QGChasing.cpd_step_exists_unique
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:30:31.636179+00:00
-- url     : https://prove2.me/theorems/323ac79a-ef86-4041-95d7-159cf84d4830
-- title:
--   Algorithm 1 is well defined: each CPD update exists, is unique and is feasible
-- statement:
--   Throughout, $\kappa\ge1$, $X\subseteq\mathbb R^d$ is nonempty, closed and convex, the hitting cost $f=f_t$ lies in $\mathcal F_\kappa$, $p=x_{t-1}\in X$ is the previous decision, $v=v_t$ is the global minimizer of $f$, and $g=g_t=f-f(v)$ is the shifted cost. $v^X$ denotes the point of $\arg\min_{z\in X}g(z)$ nearest to $p$, and $r=\frac1{2\kappa^{1/3}}$, $\beta=1+3r$, $C=\frac{32}{7}(1+\kappa^{1/3})$ are the parameters (3).
--
--   From every previous decision $p\in X$, Algorithm 1 has exactly one next decision $x_t$ (lines 2–7), and $x_t\in X$. That is, the global minimizer $v_t$, the nearest constrained minimizer $v^X_t$, the case distinction of line 4, the smallest balancing parameter $\mu_t$, the proximal point $y_t$ and the final projection are all determined, and the result is feasible.
--
--   This is the statement "every update of Algorithm 1 is well defined" on p.6. It guarantees that the trajectory in Theorem 1.1 exists and is unique from every $x_0\in X$.
--
--   Differences from the source:
--   - encoding: Π_S, the arg min of line 3, the proximal point (8) and the smallest μ_t, computed by Algorithm 1 → relational predicates: membership in the published nearest-point set SuperPolyak.nearestPoints, IsProxPoint and IsCPDBalanced (minimality of μ_t as a clause); reason: no junk-valued projection or sInf; each predicate has exactly one solution (Lemma 4.1 and cpd_step_exists_unique)
--   - generalization: x_{t−1} is the previous decision of a CPD run → any p ∈ X; reason: the argument uses only x_{t−1} ∈ X; every CPD decision lies in X (cpd_step_exists_unique), so the round of a run is an instance
--   - reading: every update of Algorithm 1 is well defined → exactly one CPD decision exists, and it lies in X; reason: well defined = exists and is unique (the proof of Lemma 4.1 proves each object unique); feasibility is the role of the projection (p.6)
-- source:
--   He–Yang–Jiang–Zhang, Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth, STOC 2027 submission (manuscript sha256 ba253cd3…02239), p.6, the paragraph after Lemma 4.1 ("every update of Algorithm 1 is well defined"); proof of Lemma 4.1, pp.12–14

import Mathlib
import Definitions.Def_QGChasing_InFkappa
import Definitions.Def_QGChasing_IsCPDStep

namespace QGChasing

/-- **Algorithm 1 is well defined** (He–Yang–Jiang–Zhang, *Optimal Competitive Ratios for Chasing Convex Functions with Quadratic Growth*, STOC 2027 submission manuscript (sha256 ba253cd3…02239), p.6, the sentence after Lemma 4.1: "Therefore, every
update of Algorithm 1 is well defined"; proof of Lemma 4.1, pp.12–14). For every `κ ≥ 1`, nonempty
closed convex `X`, hitting cost `f ∈ F_κ` and previous decision `p ∈ X`, there is exactly one CPD
decision `x` (Algorithm 1, lines 2–7), and it is feasible: `x ∈ X`.

**Formalization Note** "Well defined" is read as existence and uniqueness of the update; the
proof of Lemma 4.1 shows that `v_t`, `v^X_t`, each proximal point, the smallest `μ_t` and the final
projection are unique. `X` is nonempty because `p ∈ X`. -/
theorem cpd_step_exists_unique {d : ℕ} (κ : ℝ) (hκ : 1 ≤ κ) (X : Set (EuclideanSpace ℝ (Fin d))) (hXc : IsClosed X) (hXcv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : InFkappa κ f) (p : EuclideanSpace ℝ (Fin d)) (hp : p ∈ X) :
    (∃! x : EuclideanSpace ℝ (Fin d), IsCPDStep κ X f p x) ∧ ∀ x : EuclideanSpace ℝ (Fin d), IsCPDStep κ X f p x → x ∈ X := by sorry

end QGChasing
