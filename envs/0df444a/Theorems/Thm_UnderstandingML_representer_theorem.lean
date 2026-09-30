-- Prove2me | Theorems.Thm_UnderstandingML_representer_theorem
-- name    : UnderstandingML.representer_theorem
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:46:29.064321+00:00
-- url     : https://prove2.me/theorems/aac7a93f-c172-4626-9fa6-7468a64b253f
-- title:
--   Theorem 16.1 (Representer Theorem): if (16.2) has an optimal solution, some optimal solution is w = ∑ᵢ αᵢ ψ(xᵢ)
-- statement:
--   **Theorem 16.1 (Representer Theorem).** Assume that $\psi$ is a mapping from $X$ to a Hilbert space. Then, there exists a vector $\alpha \in \mathbb{R}^m$ such that $w = \sum_{i=1}^m \alpha_i\psi(x_i)$ is an optimal solution of Equation (16.2), $\min_w f(\langle w, \psi(x_1)\rangle, \dots, \langle w, \psi(x_m)\rangle) + R(\|w\|)$, where $R$ is monotonically nondecreasing.
--
--   Formally: assuming (16.2) has an optimal solution (as the book's proof does), with $R$ nondecreasing on $[0, \infty)$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §16.2 p. 218, Theorem 16.1 with its proof

import Definitions.Def_UnderstandingML_Kernel

open MeasureTheory
open scoped InnerProductSpace

universe u

namespace UnderstandingML

/-- **Theorem 16.1 (Representer Theorem)** (p. 218). Assume that `ψ` is a mapping from `X` to a
Hilbert space, and that the problem (16.2), `min_w f(⟨w, ψ(x₁)⟩, …, ⟨w, ψ(x_m)⟩) + R(‖w‖)` with
`R` nondecreasing, has an optimal solution. Then there exists a vector `α ∈ ℝ^m` such that
`w = ∑ᵢ αᵢ ψ(xᵢ)` is an optimal solution of Equation (16.2). -/
theorem representer_theorem {X : Type u} {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {m : ℕ} (ψ : X → F) (x : Fin m → X)
    (f : (Fin m → ℝ) → ℝ) (R : ℝ → ℝ) (hR : MonotoneOn R (Set.Ici 0)) (wstar : F)
    (hopt : ∀ w, kernelObjective ψ x f R wstar ≤ kernelObjective ψ x f R w) :
    ∃ α : Fin m → ℝ, ∀ w,
      kernelObjective ψ x f R (∑ i, α i • ψ (x i)) ≤ kernelObjective ψ x f R w := by sorry

end UnderstandingML
