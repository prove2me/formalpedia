-- Prove2me | Theorems.Thm_ShorNonsmooth_Ellipsoid_ellipsoid_volume_formula
-- name    : ShorNonsmooth.Ellipsoid.ellipsoid_volume_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T16:17:48.880984+00:00
-- url     : https://prove2.me/theorems/ab376ee8-169e-4687-bb22-cee5fad47cc8
-- title:
--   p. 87 — the localizing ellipsoid $\Phi_k$ has volume $v_0 R^n (n/\sqrt{n^2-1})^{nk}/\det A_k$
-- statement:
--   Let $n > 1$, $R > 0$, let $g : E_n \to E_n$ be any vector field and $x_0 \in E_n$, and run the algorithm (3.57)–(3.60) from $x_0$, $B_0 = I_n$, $h_0 = R/(n+1)$. Suppose that the first $k$ iterations are performed, i.e. $g(x_j) \ne 0$ for $j = 0, \dots, k-1$, and put $A_k = B_k^{-1}$. Then
--   $$
--   (n+1)\,h_k = R\left(\frac{n}{\sqrt{n^2-1}}\right)^{k},
--   $$
--   and for every center $c \in E_n$ the ellipsoid $\Phi_k = \{x : \|A_k(x - c)\| \le (n+1) h_k\}$ has Lebesgue volume
--   $$
--   v(\Phi_k) = v_0\, R^n \left(\frac{n}{\sqrt{n^2-1}}\right)^{nk} \Big/ \det A_k ,
--   $$
--   where $v_0$ is the volume of the closed unit ball of $E_n$.
--
--   This is the volume computation that turns the localization inequality (3.61) of Theorem 3.14 into a rate: the solution lies in an ellipsoid whose volume is known explicitly.
--
--   **Formalization Note** The book centers $\Phi_k$ at $x^*$; since Lebesgue measure is translation invariant, the statement is given for an arbitrary center, which covers both $x^*$ and the iterate $x_k$. The volume is an element of `ℝ≥0∞` and the right-hand side is `volume (closedBall 0 1) * ENNReal.ofReal (…)`.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 87, display following the proof of Theorem 3.14

import Mathlib
import Definitions.Def_ShorNonsmooth_Ellipsoid_EllipsoidMethod

open MeasureTheory

namespace ShorNonsmooth.Ellipsoid

/-- Shor (1985), p. 87, display after the proof of Theorem 3.14. Let `n > 1`, `R > 0`, and let
the algorithm (3.57)–(3.60) run for `k` iterations without stopping (`g(x_j) ≠ 0` for `j < k`).
Then `(n + 1) h_k = R (n/√(n² - 1))^k`, and for every center `c` the ellipsoid
`Φ_k = {x : ‖A_k (x - c)‖ ≤ (n + 1) h_k}`, `A_k = B_k⁻¹`, has volume
`v₀ Rⁿ (n/√(n² - 1))^{nk} / det A_k`, where `v₀` is the volume of the unit ball.
(The book centers `Φ_k` at `x*`; the volume does not depend on the center.) -/
theorem ellipsoid_volume_formula {n : ℕ} (hn : 1 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0 < R)
    (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hrun : ∀ j < k, g (ellipsoidMethod g R x₀ j).x ≠ 0) :
    ((n : ℝ) + 1) * (ellipsoidMethod g R x₀ k).h = R * ratio n ^ k ∧
    ∀ c : EuclideanSpace ℝ (Fin n),
      volume (ellipsoid (ellipsoidMethod g R x₀ k).B⁻¹ c
          (((n : ℝ) + 1) * (ellipsoidMethod g R x₀ k).h)) =
        volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) *
          ENNReal.ofReal (R ^ n * ratio n ^ (n * k) / ((ellipsoidMethod g R x₀ k).B⁻¹).det) := by sorry

end ShorNonsmooth.Ellipsoid
