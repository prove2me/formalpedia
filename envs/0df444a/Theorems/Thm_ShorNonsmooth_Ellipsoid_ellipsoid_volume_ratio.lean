-- Prove2me | Theorems.Thm_ShorNonsmooth_Ellipsoid_ellipsoid_volume_ratio
-- name    : ShorNonsmooth.Ellipsoid.ellipsoid_volume_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T16:18:24.278114+00:00
-- url     : https://prove2.me/theorems/b210f303-890d-4896-ab9b-6e2bb60ba34f
-- title:
--   p. 87 — the localizing ellipsoids shrink in volume by the ratio $q_n < 1$ per iteration
-- statement:
--   Let $n > 1$, $R > 0$, $g : E_n \to E_n$ any vector field and $x_0 \in E_n$, and run the algorithm (3.57)–(3.60). Suppose the $(k+1)$-st iteration is performed, i.e. $g(x_k) \neq 0$. With $A_j = B_j^{-1}$ and $\Phi_j = \{x : \|A_j(x - c_j)\| \le (n+1) h_j\}$ for arbitrary centers $c_k, c_{k+1}$, the volume $v(\Phi_k)$ is positive and finite, and
--   $$
--   v(\Phi_{k+1}) = q_n\, v(\Phi_k), \qquad q_n = \sqrt{\frac{n-1}{n+1}}\left(\frac{n}{\sqrt{n^2-1}}\right)^{n} < 1 .
--   $$
--
--   Thus the volume of the ellipsoid that localizes the solution according to (3.61) decreases geometrically with ratio $q_n$, which depends only on the dimension ($q_n \approx 1 - 1/(2n)$ for large $n$).
--
--   **Formalization Note** The chain of equalities printed on p. 87 carries the exponents $2$ and $1$ on $n/\sqrt{n^2-1}$ where $n$ is meant, and writes $(n-1)/(n+1)$ where $\sqrt{(n-1)/(n+1)} = \beta$ is meant; the statement uses the value of $q_n$ printed on p. 88, which is what the book's own derivation gives ($\det A_{k+1} = \det R_{1/\beta}(\xi_k)\det A_k = \beta^{-1}\det A_k$). The volumes are compared in `ℝ≥0∞`; positivity and finiteness of $v(\Phi_k)$ are stated so that the identity is the book's ratio.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 87, display following the proof of Theorem 3.14 (corrected), and p. 88, the definition of $q_n$

import Mathlib
import Definitions.Def_ShorNonsmooth_Ellipsoid_EllipsoidMethod

open MeasureTheory

namespace ShorNonsmooth.Ellipsoid

/-- Shor (1985), pp. 87–88, the volume ratio after the proof of Theorem 3.14, corrected. Let
`n > 1`, `R > 0`, and let the `(k+1)`-st iteration of (3.57)–(3.60) be performed (`g(x_k) ≠ 0`).
With `Φ_k = {x : ‖A_k (x - c)‖ ≤ (n + 1) h_k}`, `A_k = B_k⁻¹`, the volume of `Φ_k` is positive and
finite and, for any centers `c, c'`,
`v(Φ_{k+1}) = q_n v(Φ_k)` with `q_n = √((n - 1)/(n + 1)) (n/√(n² - 1))ⁿ < 1` (p. 88).
The printed chain on p. 87 carries the exponents `2` and `1` on `n/√(n² - 1)` and drops the
square root on `(n - 1)/(n + 1)`; the statement follows the value of `q_n` on p. 88. -/
theorem ellipsoid_volume_ratio {n : ℕ} (hn : 1 < n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0 < R)
    (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hstep : g (ellipsoidMethod g R x₀ k).x ≠ 0) :
    qRatio n < 1 ∧
    ∀ c c' : EuclideanSpace ℝ (Fin n),
      0 < volume (ellipsoid (ellipsoidMethod g R x₀ k).B⁻¹ c
          (((n : ℝ) + 1) * (ellipsoidMethod g R x₀ k).h)) ∧
      volume (ellipsoid (ellipsoidMethod g R x₀ k).B⁻¹ c
          (((n : ℝ) + 1) * (ellipsoidMethod g R x₀ k).h)) < ⊤ ∧
      volume (ellipsoid (ellipsoidMethod g R x₀ (k + 1)).B⁻¹ c'
          (((n : ℝ) + 1) * (ellipsoidMethod g R x₀ (k + 1)).h)) =
        ENNReal.ofReal (qRatio n) *
          volume (ellipsoid (ellipsoidMethod g R x₀ k).B⁻¹ c
            (((n : ℝ) + 1) * (ellipsoidMethod g R x₀ k).h)) := by sorry

end ShorNonsmooth.Ellipsoid
