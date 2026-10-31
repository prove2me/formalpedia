-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_individualZTensorProducts
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.individualZTensorProducts
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:53:24.705551+00:00
-- url     : https://prove2.me/theorems/ff40cd5c-c132-4a74-9218-997163593a17
-- title:
--   Independent z-rotation phases for tensor products and sums
-- statement:
--   Let $n\ge1$, let $J_0=I$, $J_z=Z/2$, and $J_\pm=(X\pm iY)/2$, with respective orders $0,0,+1,-1$. For a label sequence $\nu$, put $T_\nu=\bigotimes_\ell J_{\nu_\ell}$ and write $p_{\nu,\ell}$ for the corresponding order. For any real angles $\phi_\ell$, the matrix $K_z(\boldsymbol\phi)=\bigotimes_\ell e^{-i\phi_\ell Z/2}$ is local special-unitary, and
--
--   $$K_z(\boldsymbol\phi)T_\nu K_z(\boldsymbol\phi)^\dagger=e^{-i\sum_\ell p_{\nu,\ell}\phi_\ell}T_\nu.$$
--
--   Consequently a finite complex sum $H=\sum_\lambda c_\lambda T_{\nu_\lambda}$ is sign-inverted by this same rotation if $\sum_\ell p_{\nu_\lambda,\ell}\phi_\ell$ is an odd multiple of $\pi$ for every constituent. If the sum is Hermitian and traceless, it generates a type-I reversible evolution. The algebraic phase identity itself does not require Hermiticity.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 7, (37)–(40): individual z rotations of tensor products and sums

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- (37)–(40), PDF pp.7–8. Tensor operators are complex; Hermiticity
and trace zero are required only for the physical TypeI conclusion. -/
theorem individualZTensorProducts {n : ℕ} (hn : 0 < n) :
    (∀ phi : Fin n → ℝ, ∃ K : LocalSU n, localMatrix K = individualZRotation phi) ∧
    (∀ (nu : Fin n → Fin 4) (phi : Fin n → ℝ),
      adjointConjugation (individualZRotation phi) (tensorMonomial nu) =
        Complex.exp (-Complex.I * ((∑ l, (factorOrder (nu l) : ℝ) * phi l : ℝ) : ℂ)) •
          tensorMonomial nu) ∧
    (∀ (m : ℕ) (nu : Fin m → Fin n → Fin 4) (c : Fin m → ℂ)
      (phi : Fin n → ℝ),
      (∀ a, OddPi (∑ l, (factorOrder (nu a l) : ℝ) * phi l)) →
      adjointConjugation (individualZRotation phi) (tensorOperatorSum nu c) = -tensorOperatorSum nu c ∧
      (IsHamiltonian (tensorOperatorSum nu c) → TypeI (tensorOperatorSum nu c))) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
