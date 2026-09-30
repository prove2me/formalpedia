-- Prove2me | Theorems.Thm_UnderstandingML_perceptron_convergence
-- name    : UnderstandingML.perceptron_convergence
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:53:56.233017+00:00
-- url     : https://prove2.me/theorems/1889e031-cdcc-486c-9e0e-434750643d54
-- title:
--   Theorem 9.1 (Perceptron): for a separable sample with B = min{‖w‖ : yᵢ⟨w,xᵢ⟩ ≥ 1} and R = maxᵢ‖xᵢ‖, the Batch Perceptron stops after at most (RB)² iterations with all yᵢ⟨w,xᵢ⟩ > 0
-- statement:
--   **Theorem 9.1.** Assume that $(x_1, y_1), \dots, (x_m, y_m)$ is separable, let $B = \min\{\|w\| : \forall i \in [m],\ y_i\langle w, x_i\rangle \ge 1\}$, and let $R = \max_i \|x_i\|$. Then the Perceptron algorithm stops after at most $(RB)^2$ iterations, and when it stops it holds that $\forall i \in [m],\ y_i\langle w^{(t)}, x_i\rangle > 0$.
--
--   Formally (labels in $\{\pm 1\}$): every run of the Batch Perceptron of $T$ iterations has $T \le (RB)^2$; and there is a run of at most $(RB)^2$ iterations after which every example satisfies $y_i\langle w^{(T)}, x_i\rangle > 0$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §9.1.2 pp. 120-121, Theorem 9.1 with its proof

import Definitions.Def_UnderstandingML_Linear

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 9.1** (p. 120). Assume that `(x₁, y₁), …, (x_m, y_m)` is separable, let
`B = min{‖w‖ : ∀ i ∈ [m], yᵢ⟨w, xᵢ⟩ ≥ 1}` and let `R = maxᵢ ‖xᵢ‖`. Then the Perceptron algorithm
stops after at most `(RB)²` iterations, and when it stops it holds that
`∀ i ∈ [m], yᵢ⟨w⁽ᵗ⁾, xᵢ⟩ > 0`. Stated as: every run of the Batch Perceptron has at most `(RB)²`
iterations, and some run of at most `(RB)²` iterations ends with all examples correctly
classified (the stopping condition). -/
theorem perceptron_convergence {d m : ℕ} (x : Fin m → Vec d) (y : Fin m → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) (hsep : Separable x y) :
    (∀ (w : ℕ → Vec d) (T : ℕ), IsPerceptronRun x y w T →
        (T : ℝ) ≤ (radius x * marginNorm x y) ^ 2) ∧
    ∃ (w : ℕ → Vec d) (T : ℕ), IsPerceptronRun x y w T ∧
      (T : ℝ) ≤ (radius x * marginNorm x y) ^ 2 ∧ ∀ i, 0 < y i * ⟪w T, x i⟫_ℝ := by sorry

end UnderstandingML
