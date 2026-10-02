-- Prove2me | Theorems.Thm_ShorNonsmooth_RAlgorithm_exists_dependent_point_at_limit_level
-- name    : ShorNonsmooth.RAlgorithm.exists_dependent_point_at_limit_level
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T16:15:19.883986+00:00
-- url     : https://prove2.me/theorems/5e1e0854-f737-408e-8950-806ce8986e90
-- title:
--   Theorem 3.12 — the level set $\{f = f_\infty\}$ contains a point with linearly dependent $G_f$
-- statement:
--   Let the assumptions of Theorem 3.11 and condition (3.50) hold: $n \ge 1$, $f \in K$ with $f(x) \to +\infty$ as $\|x\| \to \infty$, $\alpha > 1$, and $\{x_k\}$ a sequence constructed by the $r(\alpha)$-algorithm applied to $f$ with $\|x_{k+1} - x_k\| \to 0$. The values $f(x_k)$ are nonincreasing and bounded below, so
--   $$
--   f_\infty = \lim_{k \to \infty} f(x_k) > -\infty
--   $$
--   exists. Then the level set $U = \{x : f(x) = f_\infty\}$ contains a point $x^*$ such that the set of vectors $G_f(x^*)$ is linearly dependent.
--
--   For a smooth $f$ (one piece) linear dependence of $G_f(x^*) = \{\nabla f(x^*)\}$ means $\nabla f(x^*) = 0$; in general it is a generalized stationarity condition. The theorem says the monotone values of the $r$-algorithm settle at a level containing such a point.
--
--   **Formalization Note** $f_\infty$ is written as $\inf_k f(x_k)$, which equals the limit because the values are nonincreasing and bounded below. Linear dependence of the set $G_f(x^*)$ is `¬ LinearIndependent` of the family indexed by the elements of the set (a set containing $0$ is dependent).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 84, Theorem 3.12 (proof pp. 84–85); $f_\infty$ defined on p. 82

import Mathlib
import Definitions.Def_ShorNonsmooth_RAlgorithm_RAlgorithm

open scoped InnerProductSpace
open Filter Topology

namespace ShorNonsmooth.RAlgorithm

/-- Shor (1985), p. 84, **Theorem 3.12**. Under the assumptions of Theorem 3.11 and condition
(3.50), let `f_∞ = lim_{k→∞} f(x_k)` (the values `f(x_k)` are nonincreasing and bounded below,
p. 82, so the limit is their infimum). Then the set `U = {x : f(x) = f_∞}` contains a point `x*`
such that the set of vectors `G_f(x*)` is linearly dependent. -/
theorem exists_dependent_point_at_limit_level {n : ℕ} (hn : 0 < n) (P : KRep n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : P.Forms f)
    (hf_coercive : Tendsto f (cocompact (EuclideanSpace ℝ (Fin n))) atTop)
    (α : ℝ) (hα : 1 < α)
    (x gt g : ℕ → EuclideanSpace ℝ (Fin n))
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (h : ℕ → ℝ)
    (hrun : IsRun P f α 0 x gt g B h)
    (hstep : Tendsto (fun k => ‖x (k + 1) - x k‖) atTop (𝓝 0)) :
    ∃ xs : EuclideanSpace ℝ (Fin n), f xs = ⨅ k, f (x k) ∧
      ¬ LinearIndependent ℝ ((↑) : P.Gf xs → EuclideanSpace ℝ (Fin n)) := by sorry

end ShorNonsmooth.RAlgorithm
