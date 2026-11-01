-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P47_decorrelation_achievability
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P47.decorrelation_achievability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:13:34.744894+00:00
-- url     : https://prove2.me/theorems/867c6bad-e32b-4445-a63e-5ad42e2cfc56
-- title:
--   Proposition II.2: one-sided uniform decorrelation achievability
-- statement:
--   Let $\rho_{AB}$ be any density matrix on finite nonzero complex spaces. For every $\epsilon>0$ there is an integer $n_0\ge1$ such that for every $n\ge n_0$ there is a finite ensemble of $N\ge1$ unitaries acting only on Alice's $n$ copies, all with probability $1/N$. Its channel $R$ satisfies
--
--   $$\inf_{\omega_A,\omega_B}\|R(\rho^{\otimes n})-\omega_A\otimes\omega_B\|_1\le\epsilon,\qquad\log_2N\le n\bigl(I(A:B)_\rho+\epsilon\bigr),$$
--
--   where the product-state approximation is attained by normalized local density matrices. The full trace norm is used. This supplies one-sided uniform randomness achievability with both an arbitrary error tolerance and an arbitrary per-copy rate slack.
-- source:
--   On the quantum, classical and total amount of correlations in a quantum state, arXiv:quant-ph/0410091v2, PDF p. 3, Proposition II.2: one-sided uniform decorrelation achievability

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P47

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies localProduct)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon Config)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3--4, Proposition II.2: both tolerance and per-copy rate slack are eps. -/
theorem decorrelation_achievability {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (eps : ℝ) (heps : 0 < eps) :
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      ∃ R : COLUR (Copies A n) (Copies B n), R.allowed .alice ∧
        (∀ i, R.weight i = (R.count : ℝ)⁻¹) ∧
        Decorrelates (R.operation (sourcePower rho n)) eps ∧
        Real.logb 2 R.count ≤ (n : ℝ) * (mutualInformation rho + eps) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P47

end
