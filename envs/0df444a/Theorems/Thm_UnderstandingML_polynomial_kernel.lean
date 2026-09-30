-- Prove2me | Theorems.Thm_UnderstandingML_polynomial_kernel
-- name    : UnderstandingML.polynomial_kernel
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:48:10.735983+00:00
-- url     : https://prove2.me/theorems/409ba8c3-b243-4ec8-9e3d-d22370360229
-- title:
--   Example 16.1: the degree-k polynomial kernel (1 + ⟨x,x'⟩)^k on ℝⁿ is ⟨ψ(x), ψ(x')⟩ for the monomial map ψ : ℝⁿ → ℝ^{(n+1)^k}
-- statement:
--   **Example 16.1 (Polynomial Kernels).** The $k$ degree polynomial kernel is $K(x, x') = (1 + \langle x, x'\rangle)^k$. It is a kernel function: with $x_0 = x'_0 = 1$, $K(x, x') = \sum_{J \in \{0,\dots,n\}^k}\prod_{i=1}^k x_{J_i}\prod_{i=1}^k x'_{J_i}$, so for $\psi : \mathbb{R}^n \to \mathbb{R}^{(n+1)^k}$ with coordinate $\prod_{i=1}^k x_{J_i}$ at $J$, $K(x, x') = \langle\psi(x), \psi(x')\rangle$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §16.2 p. 220, Example 16.1 with its derivation

import Definitions.Def_UnderstandingML_Kernel

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Example 16.1 (Polynomial Kernels)** (p. 220). The degree-`k` polynomial kernel
`K(x, x') = (1 + ⟨x, x'⟩)^k` on `ℝ^n` is a kernel function: there is a mapping `ψ : ℝ^n → ℝ^{(n+1)^k}`,
indexed by `J ∈ {0, 1, …, n}^k` with coordinate `∏ᵢ x_{Jᵢ}` (where `x₀ = 1`), such that
`K(x, x') = ⟨ψ(x), ψ(x')⟩`. -/
theorem polynomial_kernel (n k : ℕ) :
    ∃ ψ : Vec n → EuclideanSpace ℝ (Fin k → Fin (n + 1)),
      ∀ x x' : Vec n, polynomialKernel k x x' = ⟪ψ x, ψ x'⟫_ℝ := by sorry

end UnderstandingML
