-- Prove2me | Theorems.Thm_SimpleSSA_Monotone_eq_5
-- name    : SimpleSSA.Monotone.eq_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:02.033069+00:00
-- url     : https://prove2.me/theorems/fdc3f27e-6af3-4577-9530-e9f3424ff89d
-- title:
--   (5), p. 2 — conditional entropy as a relative entropy: S(B|A) = ln d_B − S(ρ_AB ‖ ρ_A ⊗ I_B/d_B)
-- statement:
--   Let $\rho_{AB}$ be a density matrix on a composite finite-dimensional system $AB$, let $\rho_A = \operatorname{tr}_B\rho_{AB}$, and let $d_B$ be the dimension of $B$. The conditional entropy is $S(B|A) \equiv S(\rho_{AB}) - S(\rho_A)$, with $S(\rho) = -\operatorname{tr}(\rho\ln\rho)$. Then
--
--   $$S(B|A) = \ln d_B - S\Big(\rho_{AB}\,\Big\|\,\rho_A\otimes\frac{I_B}{d_B}\Big),$$
--
--   where $S(\cdot\|\cdot)$ is the relative entropy (3).
--
--   The identity rewrites conditional entropies as relative entropies; applied to the systems of (2), it turns strong subadditivity into the relative-entropy inequality (6).
--
--   **Formalization Note** No invertibility is assumed. The support of $\rho_{AB}$ always lies in the support of $\rho_A\otimes I_B$, so the real-valued relative entropy of the formalization (logarithms by functional calculus, with $\ln 0 = 0$ on kernels) is the paper's finite value for every density matrix $\rho_{AB}$. The page prints the denominator as $d_b$; it is $d_B$, the dimension of $B$. Logarithms are natural.
-- source:
--   Nielsen & Petz, A simple proof of the strong subadditivity inequality, arXiv:quant-ph/0408130v3, p. 2, (5); S(·|·) defined on p. 1

import Mathlib
import Definitions.Def_SimpleSSA_Monotone_Basic

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix

namespace SimpleSSA.Monotone

open TroppMatrixConcentration QAlgorithms WildeQIT

/-- (5), p. 2: `S(B|A) = ln d_B − S(ρ_AB ‖ ρ_A ⊗ I_B/d_B)`, with `S(B|A) = S(ρ_AB) − S(ρ_A)`,
for every density matrix `ρ_AB`. -/
theorem eq_5 {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) :
    entropy ρ - entropy (partialTraceRight ρ) =
      Real.log (Fintype.card B) - relEntropy ρ (partialTraceRight ρ ⊗ₖ maximallyMixed B) := by sorry

end SimpleSSA.Monotone
