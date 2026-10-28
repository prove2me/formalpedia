-- Prove2me | Theorems.Thm_SimpleSSA_Monotone_petz_map_properties
-- name    : SimpleSSA.Monotone.petz_map_properties
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:02.426013+00:00
-- url     : https://prove2.me/theorems/f2c5546e-b7be-4ef4-a251-517058e4849d
-- title:
--   pp. 4–5 — properties (1)–(3) of 𝒰(X) = (Xρ_A^{−1/2} ⊗ I_B)ρ_AB^{1/2}: 𝒰†Δ_AB𝒰 = Δ_A, 𝒰(ρ_A^{1/2}) = ρ_AB^{1/2}, 𝒰†𝒰 = ℐ_A, and its adjoint
-- statement:
--   Let $\rho_{AB}$ and $\sigma_{AB}$ be invertible density matrices on a composite finite-dimensional system $AB$, with reduced density matrices $\rho_A = \operatorname{tr}_B\rho_{AB}$ and $\sigma_A = \operatorname{tr}_B\sigma_{AB}$. Let $\Delta_{AB}(X) = \sigma_{AB}X\rho_{AB}^{-1}$ and $\Delta_A(X) = \sigma_A X\rho_A^{-1}$ be the relative modular operators on $M(AB)$ and $M(A)$, and define the linear map $\mathcal U : M(A)\to M(AB)$ by
--
--   $$\mathcal U(X) = (X\rho_A^{-1/2}\otimes I_B)\,\rho_{AB}^{1/2}.$$
--
--   With adjoints taken for the Hilbert–Schmidt inner products $\langle X,Y\rangle = \operatorname{tr}(X^\dagger Y)$:
--
--   1. $\mathcal U^\dagger\Delta_{AB}\,\mathcal U = \Delta_A$;
--   2. $\mathcal U(\rho_A^{1/2}) = \rho_{AB}^{1/2}$;
--   3. $\mathcal U^\dagger\mathcal U = \mathcal I_A$, the identity map of $M(A)$, i.e. $\mathcal U$ is an isometry from $M(A)$ to $M(AB)$;
--   4. the map $\mathcal U^\dagger(Y) = \operatorname{tr}_B\big(Y\rho_{AB}^{1/2}(\rho_A^{-1/2}\otimes I_B)\big)$ is the adjoint of $\mathcal U$: $\langle\mathcal U^\dagger(Y),X\rangle = \langle Y,\mathcal U(X)\rangle$ for all $X\in M(A)$, $Y\in M(AB)$.
--
--   These are the properties (1)–(3) that the proof of monotonicity (4) requires of $\mathcal U$ (p. 4), together with the explicit adjoint stated on p. 5. With them, Lemma 2 applied to the isometry $\mathcal U$ and Lemma 1 give $-\ln(\mathcal U^\dagger\Delta_{AB}\mathcal U)\le-\mathcal U^\dagger\ln(\Delta_{AB})\mathcal U$, the key step (10).
--
--   **Formalization Note** Invertibility of $\rho_{AB}$ and $\sigma_{AB}$ is the paper's §3 assumption (p. 3). Linear maps on matrices are matrices in the row-major vectorization $\operatorname{vec}X = (X_{ij})_{(i,j)}$, in which the Hilbert–Schmidt inner product is the standard one; so $\mathcal U$ is the matrix whose column $(a,a')$ is $\operatorname{vec}\,\mathcal U(E_{aa'})$, $\mathcal U^\dagger$ in items 1 and 3 is its conjugate transpose, $\Delta_{AB} = \sigma_{AB}\otimes(\rho_{AB}^{-1})^T$, $\Delta_A = \sigma_A\otimes(\rho_A^{-1})^T$, and $\mathcal I_A$ is the identity matrix on $\mathbb C^{A\times A}$. $\rho^{\pm1/2}$ are taken by functional calculus.
-- source:
--   Nielsen & Petz, A simple proof of the strong subadditivity inequality, arXiv:quant-ph/0408130v3, p. 4, properties (1)–(3) of 𝒰; p. 5, definition of 𝒰, its adjoint 𝒰†, and "Direct calculation now shows that 𝒰†Δ_AB𝒰 = Δ_A and 𝒰†𝒰 = ℐ_A"

import Mathlib
import Definitions.Def_SimpleSSA_Monotone_Basic

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix

namespace SimpleSSA.Monotone

open TroppMatrixConcentration QAlgorithms WildeQIT

/-- pp. 4–5: for invertible density matrices `ρ_AB`, `σ_AB` (the §3 assumption, p. 3), the map
`𝒰(X) = (X ρ_A^{−1/2} ⊗ I_B) ρ_AB^{1/2}` satisfies (1) `𝒰†Δ_AB𝒰 = Δ_A`, (2) `𝒰(ρ_A^{1/2}) = ρ_AB^{1/2}`,
(3) `𝒰†𝒰 = ℐ_A` (an isometry `M(A) → M(AB)`), and `𝒰†(Y) = tr_B(Y ρ_AB^{1/2}(ρ_A^{−1/2} ⊗ I_B))` is its
adjoint for the Hilbert–Schmidt inner product. -/
theorem petz_map_properties {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (ρ σ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) (hρ_inv : ρ.PosDef)
    (hσ : IsDensityMatrix σ) (hσ_inv : σ.PosDef) :
    (petzMatrix ρ)ᴴ * modularOp ρ σ * petzMatrix ρ =
        modularOp (partialTraceRight ρ) (partialTraceRight σ) ∧
      petzMap ρ (sqrtM (partialTraceRight ρ)) = sqrtM ρ ∧
      (petzMatrix ρ)ᴴ * petzMatrix ρ = 1 ∧
      ∀ (X : Matrix A A ℂ) (Y : Matrix (A × B) (A × B) ℂ),
        hsInner (petzAdjoint ρ Y) X = hsInner Y (petzMap ρ X) := by sorry

end SimpleSSA.Monotone
