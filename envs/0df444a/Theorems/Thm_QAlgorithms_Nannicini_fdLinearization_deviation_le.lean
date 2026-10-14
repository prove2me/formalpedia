-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_fdLinearization_deviation_le
-- name    : QAlgorithms.Nannicini.fdLinearization_deviation_le
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:45:49.108534+00:00
-- url     : https://prove2.me/theorems/2ecc113c-2b0d-483c-9532-df0cfd422656
-- title:
--   Deviation from the finite-difference linearization on the ℓ1 ball is at most (η²/2)Δ^(η)f(z)
-- statement:
--   Let $d \ge 0$, $\eta > 0$ and $z \in \mathbb{R}^d$, and let $f : B_1(z,\eta) \to \mathbb{R}$ be convex, where $B_1(z,\eta) = \{w : \|z - w\|_1 \le \eta\}$. Let $\nabla^{(\eta)} f(z)$ and $\Delta^{(\eta)} f(z)$ be the finite-difference gradient and Laplace approximation,
--
--   $$
--   \nabla^{(\eta)} f(z)_j = \frac{f(z+\eta e_j) - f(z-\eta e_j)}{2\eta}, \qquad \Delta^{(\eta)} f(z) = \sum_{j=1}^d \frac{f(z+\eta e_j) - 2 f(z) + f(z-\eta e_j)}{\eta^2}.
--   $$
--
--   Then for every $y \in \mathbb{R}^d$ with $\|y\|_1 \le \eta$,
--
--   $$
--   \bigl|f(z+y) - f(z) - \langle \nabla^{(\eta)} f(z), y\rangle\bigr| \le \frac12\,\eta^2\,\Delta^{(\eta)} f(z),
--   $$
--
--   that is, the supremum of the left side over $y \in B_1(0,\eta)$ is at most $\frac12 \eta^2 \Delta^{(\eta)} f(z)$. Here $\langle\cdot,\cdot\rangle$ is the standard inner product.
--
--   The Laplace approximation therefore controls how far $f$ is from linear on a small ball around $z$, which is the hypothesis Jordan's gradient algorithm needs when it is applied to the height function.
--
--   **Formalization Note** The supremum is stated as a bound at every point of the ball. The function is total on $\mathbb{R}^d$; only its values on $B_1(z,\eta)$ are used.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 123, Lemma 5.32. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_GradientMethods
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open MeasureTheory



/-- Nannicini p.123, Lemma 5.32 (Lem. 17 in van Apeldoorn et al. 2020a). Let `η > 0`,
`z ∈ ℝ^d`, and `f : B_1(z, η) → ℝ` convex. Then
`sup_{y ∈ B_1(0, η)} |f(z + y) − f(z) − ⟨∇^(η) f(z), y⟩| ≤ (1/2) η² Δ^(η) f(z)`.

The supremum is unfolded as the bound at every `y ∈ B_1(0, η)`; `⟨·, ·⟩` is the standard inner
product of `ℝ^d`. -/
theorem fdLinearization_deviation_le {d : ℕ} (η : ℝ) (hη : 0 < η) (z : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (hf : ConvexOn ℝ (ballL1 z η) f)
    (y : Fin d → ℝ) (hy : y ∈ ballL1 0 η) :
    |f (z + y) - f z - ∑ j, fdGradient η f z j * y j| ≤ 2⁻¹ * η ^ 2 * fdLaplacian η f z := by
  sorry


end QAlgorithms.Nannicini
