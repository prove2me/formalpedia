-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_fdLaplacian_average_le
-- name    : QAlgorithms.Nannicini.fdLaplacian_average_le
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:45:41.154518+00:00
-- url     : https://prove2.me/theorems/bb92b758-7b5b-4c1e-af30-c0947799e901
-- title:
--   The Laplace approximation is at most dL/r on average over a cube
-- statement:
--   Let $d \ge 0$, $x \in \mathbb{R}^d$ and $\eta, r, L \in \mathbb{R}$ with $0 < \eta < r$. Write $B_\infty(x,s) = \{y \in \mathbb{R}^d : |x_i - y_i| \le s \text{ for all } i\}$ for the cube of half-side $s$. Let $f : B_\infty(x, r+\eta) \to \mathbb{R}$ be convex and $L$-Lipschitz with respect to the Euclidean norm, i.e. $|f(y) - f(y')| \le L\|y - y'\|_2$ for all $y, y'$ in the cube. Let
--
--   $$
--   \Delta^{(\eta)} f(z) = \sum_{j=1}^d \frac{f(z+\eta e_j) - 2 f(z) + f(z-\eta e_j)}{\eta^2}
--   $$
--
--   be the finite-difference Laplace approximation. Then, for $z$ drawn uniformly at random from $B_\infty(x,r)$,
--
--   $$
--   \mathbb{E}_{z \in B_\infty(x,r)}\, \Delta^{(\eta)} f(z) = \frac{1}{(2r)^d} \int_{B_\infty(x,r)} \Delta^{(\eta)} f(z)\, dz \le \frac{dL}{r}.
--   $$
--
--   Convexity and Lipschitz continuity do not bound the Laplace approximation at a single point (for $f(x) = |x|$ it equals $2/\eta$ at $0$), but this lemma bounds it on average over a random point, which is what makes the finite-difference gradient at a random point a good subgradient estimate.
--
--   **Formalization Note** The expectation is the average of $\Delta^{(\eta)} f$ over the cube with respect to Lebesgue measure on $\mathbb{R}^d$. The book does not say which norm the Lipschitz condition uses; the Euclidean norm is its convention for an unsubscripted norm. The function is total on $\mathbb{R}^d$; only its values on $B_\infty(x,r+\eta)$ are used.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 122, Lemma 5.30. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_GradientMethods
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open MeasureTheory


/-- Nannicini p.122, Lemma 5.30 (Lem. 11 in van Apeldoorn et al. 2020a). Let `0 < η < r`, and
let `f : B_∞(x, r + η) → ℝ` be convex and `L`-Lipschitz. Then
`E_{z ∈ B_∞(x, r)} Δ^(η) f(z) ≤ dL/r`, the expectation over a uniformly random point `z` of the
cube `B_∞(x, r)` (the average with respect to Lebesgue measure on `ℝ^d`).

The Lipschitz condition is with respect to the Euclidean norm (the book's convention for a norm
without subscript, p.11). -/
theorem fdLaplacian_average_le {d : ℕ} (η r L : ℝ) (hη : 0 < η) (hηr : η < r) (x : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (hf : ConvexOn ℝ {y | ∀ i, |x i - y i| ≤ r + η} f)
    (hL : ∀ y ∈ {y : Fin d → ℝ | ∀ i, |x i - y i| ≤ r + η},
      ∀ y' ∈ {y : Fin d → ℝ | ∀ i, |x i - y i| ≤ r + η},
        |f y - f y'| ≤ L * Real.sqrt (∑ i, (y i - y' i) ^ 2)) :
    ⨍ z in {y : Fin d → ℝ | ∀ i, |x i - y i| ≤ r}, fdLaplacian η f z ≤ d * L / r := by
  sorry



end QAlgorithms.Nannicini
