-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_normalized_choi_covariance
-- name    : QAlgorithms.Papers.Independent.Information100.P56.normalized_choi_covariance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:29:53.769989+00:00
-- url     : https://prove2.me/theorems/6a6269d4-1be6-4d9f-a95c-23150136c740
-- title:
--   Appendix A, Eq.(A1): normalized Choi covariance
-- statement:
--   Let $\mathcal N$ be a finite-dimensional quantum channel with nonzero input and output spaces, and let $U_g,V_g$ be input and output unitaries in a fixed basis. Write $d$ for the input dimension, $|\Phi\rangle=d^{-1/2}\sum_i|i,i\rangle$ and $J=(\mathrm{id}\otimes\mathcal N)(|\Phi\rangle\langle\Phi|)$, with reference factor first. Covariance at each $g$ is equivalent to
--
--   $$J=(U_g^T\otimes V_g^\dagger)J(U_g^T\otimes V_g^\dagger)^\dagger.$$
--
--   This is equivalent to $[J,\overline U_g\otimes V_g]=0$. The normalization is $1/d$ in matrix-unit coordinates, and the transpose and conjugate refer to the chosen basis.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 26, Appendix A, Eq.(A1): normalized Choi covariance

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Appendix A, p.26, Eq.(A1): normalized Choi covariance and the equivalent
commutation formulation. The input basis and reference-first factor order are fixed. -/
theorem normalized_choi_covariance
    {G A B : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (N : QAlgorithms.Superop A B) (hN : QAlgorithms.IsChannel N)
    (U : G → Matrix.unitaryGroup A ℂ) (V : G → Matrix.unitaryGroup B ℂ)
    : ∀ g,
      let J := normalizedChoi N
      let R := Matrix.kronecker (U g : Matrix A A ℂ)ᵀ (V g : Matrix B B ℂ)ᴴ
      let C := Matrix.kronecker (fun i j => conj ((U g : Matrix A A ℂ) i j))
        (V g : Matrix B B ℂ)
      ((∀ rho, N ((U g : Matrix A A ℂ) * rho * (U g : Matrix A A ℂ)ᴴ) =
        (V g : Matrix B B ℂ) * N rho * (V g : Matrix B B ℂ)ᴴ) ↔ J = R * J * Rᴴ) ∧
      (J = R * J * Rᴴ ↔ Commute J C) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
