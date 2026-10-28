-- Prove2me | Theorems.Thm_SimpleSSA_Monotone_eq_7
-- name    : SimpleSSA.Monotone.eq_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:06.17891+00:00
-- url     : https://prove2.me/theorems/c8a05142-9c3b-43dc-a6db-b8cb82565ee6
-- title:
--   (7), p. 4 — relative entropy through the relative modular operator: S(ρ‖σ) = ⟨ρ^{1/2}, −ln(Δ)(ρ^{1/2})⟩
-- statement:
--   Let $\rho$ and $\sigma$ be invertible density matrices on a finite-dimensional system $A$. Let $\Delta(X) = \sigma X\rho^{-1}$ be the relative modular operator, a strictly positive linear map on $M(A)$ for the Hilbert–Schmidt inner product $\langle X,Y\rangle = \operatorname{tr}(X^\dagger Y)$, and let $\ln(\Delta)$ be its logarithm, obtained by diagonalizing $\Delta$ and taking the logarithm of its eigenvalues. Then the relative entropy $S(\rho\|\sigma) = \operatorname{tr}(\rho\ln\rho - \rho\ln\sigma)$ satisfies
--
--   $$S(\rho\|\sigma) = \big\langle \rho^{1/2},\, -\ln(\Delta)(\rho^{1/2})\big\rangle .$$
--
--   The identity combines the two logarithms of the relative entropy, which need not commute, into the logarithm of a single positive map. It is the form in which monotonicity (4) is proved in §3, through (8)–(12).
--
--   **Formalization Note** Invertibility of $\rho$ and $\sigma$ is the paper's own standing assumption of §3 (p. 3: "In defining this operator we will assume that $\rho$ and $\sigma$ are invertible"). Linear maps on matrices are represented by matrices on $\mathbb C^{A\times A}$ in the row-major vectorization $\operatorname{vec}X = (X_{ij})_{(i,j)}$; then $\Delta$ is the Kronecker matrix $\sigma\otimes(\rho^{-1})^T$ and $\ln(\Delta)$ is its matrix logarithm by functional calculus, exactly the p. 4 definition. The equality is stated in $\mathbb C$, so it also asserts that the inner product is real. Logarithms are natural.
-- source:
--   Nielsen & Petz, A simple proof of the strong subadditivity inequality, arXiv:quant-ph/0408130v3, p. 4, (7); invertibility assumption p. 3

import Mathlib
import Definitions.Def_SimpleSSA_Monotone_Basic

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix

namespace SimpleSSA.Monotone

open TroppMatrixConcentration QAlgorithms

/-- (7), p. 4: for invertible density matrices `ρ`, `σ` (the §3 assumption, p. 3),
`S(ρ‖σ) = ⟨ρ^{1/2}, −ln(Δ)(ρ^{1/2})⟩`, where `ln(Δ)` is the logarithm of the relative modular
operator `Δ(X) = σ X ρ⁻¹` as a strictly positive linear map on matrices. -/
theorem eq_7 {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    (ρ σ : Matrix A A ℂ) (hρ : IsDensityMatrix ρ) (hρ_inv : ρ.PosDef)
    (hσ : IsDensityMatrix σ) (hσ_inv : σ.PosDef) :
    (relEntropy ρ σ : ℂ) =
      hsInner (sqrtM ρ) (applyHS (-(matrixLog (modularOp ρ σ))) (sqrtM ρ)) := by sorry

end SimpleSSA.Monotone
