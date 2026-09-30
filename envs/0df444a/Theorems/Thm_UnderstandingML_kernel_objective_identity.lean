-- Prove2me | Theorems.Thm_UnderstandingML_kernel_objective_identity
-- name    : UnderstandingML.kernel_objective_identity
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:47:07.871717+00:00
-- url     : https://prove2.me/theorems/a96ae1d2-decc-4cbc-b570-050240e13396
-- title:
--   Equation (16.3): for w = ∑ⱼ αⱼψ(xⱼ) the objective of (16.2) is f(∑ⱼ αⱼK(xⱼ,x₁), …) + R(√(∑ᵢⱼ αᵢαⱼK(xⱼ,xᵢ)))
-- statement:
--   **Equation (16.3).** Writing $w = \sum_j \alpha_j\psi(x_j)$, we have $\langle w, \psi(x_i)\rangle = \sum_j \alpha_j K(x_j, x_i)$ and $\|w\|^2 = \sum_{i,j}\alpha_i\alpha_j K(x_i, x_j)$, so instead of solving (16.2) we can solve the equivalent problem
--   $$\min_{\alpha \in \mathbb{R}^m} f\Big(\sum_j \alpha_j K(x_j, x_1), \dots, \sum_j \alpha_j K(x_j, x_m)\Big) + R\Big(\sqrt{\sum_{i,j}\alpha_i\alpha_j K(x_j, x_i)}\Big),$$
--   which needs only the Gram matrix.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §16.2 p. 219, Equation (16.3) with its derivation

import Definitions.Def_UnderstandingML_Kernel

open MeasureTheory
open scoped InnerProductSpace

universe u

namespace UnderstandingML

/-- **Equation (16.3)** (p. 219). Writing `w = ∑ⱼ αⱼ ψ(xⱼ)`, the objective of (16.2) equals
`f(∑ⱼ αⱼK(xⱼ, x₁), …, ∑ⱼ αⱼK(xⱼ, x_m)) + R(√(∑ᵢⱼ αᵢαⱼ K(xⱼ, xᵢ)))`, so that (16.2) can be solved
knowing only the Gram matrix. -/
theorem kernel_objective_identity {X : Type u} {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {m : ℕ} (ψ : X → F) (x : Fin m → X)
    (f : (Fin m → ℝ) → ℝ) (R : ℝ → ℝ) (α : Fin m → ℝ) :
    kernelObjective ψ x f R (∑ j, α j • ψ (x j)) =
      f (fun i ↦ ∑ j, α j * kernelOf ψ (x j) (x i)) +
        R (Real.sqrt (∑ i, ∑ j, α i * α j * kernelOf ψ (x j) (x i))) := by sorry

end UnderstandingML
