-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_matrixUnitSumInversion
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.matrixUnitSumInversion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:56:12.517374+00:00
-- url     : https://prove2.me/theorems/52e678b3-185d-4a99-85b4-8e7864f8312c
-- title:
--   A common angle criterion for sums of matrix units
-- statement:
--   Let $n\ge1$ and let $E_\Sigma=\sum_{\lambda=1}^m c_\lambda E_{i_\lambda j_\lambda}$, where $i_\lambda\ne j_\lambda$ and $c_\lambda\in\mathbb C$. Let $p_{\lambda\ell}$ be the eigenvalue of $Z_\ell/2$ at row $i_\lambda$ minus its eigenvalue at column $j_\lambda$. If there are real angles $\phi_\ell$ such that each $\sum_\ell p_{\lambda\ell}\phi_\ell$ is an odd multiple of $\pi$, then
--
--   $$K_z(\boldsymbol\phi) E_\Sigma K_z(\boldsymbol\phi)^\dagger=-E_\Sigma.$$
--
--   The same angle vector serves every constituent. Repeated matrix units, zero coefficients, and cancellations are permitted; the assertion is sufficient only.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 10, Proposition 2: common angle criterion for sums of matrix units

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- Proposition 2, PDF p.10, (51), with p fixed by row-minus-column Z/2
weights. Sufficiency only; coefficients may vanish or cancel. -/
theorem matrixUnitSumInversion {n m : ℕ} (hn : 0 < n)
    (i j : Fin m → QAlgorithms.Qubits n) (hij : ∀ a, i a ≠ j a)
    (c : Fin m → ℂ) (phi : Fin n → ℝ)
    (hphi : ∀ a, OddPi (∑ l, entryOrder (i a) (j a) l * phi l)) :
    adjointConjugation (individualZRotation phi) (matrixUnitSum i j c) = -matrixUnitSum i j c := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
