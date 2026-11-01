-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P84_equalityInStrongSubadditivity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P84.equalityInStrongSubadditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:07:48.758826+00:00
-- url     : https://prove2.me/theorems/17dddd46-0b05-4443-befd-40d81470e31d
-- title:
--   Theorem 3: two characterizations of equality in strong subadditivity
-- statement:
--   Let $D_{123}$ be an invertible density matrix on a tensor product $H_1\otimes H_2\otimes H_3$ of nonzero finite-dimensional complex Hilbert spaces. Let $D_{12},D_{23},D_2$ be its actual reduced densities, obtained by partial traces. Write $S(D)=-\operatorname{Tr}(D\log D)$, with natural logarithms. Each of the following conditions is separately equivalent to
--
--   $$
--   S(D_{123})+S(D_2)=S(D_{12})+S(D_{23}):
--   $$
--
--   $$
--   \begin{aligned}
--   &D_{123}^{it}(D_{12}^{-it}\otimes I_3)
--    =(I_1\otimes D_{23}^{it})(I_1\otimes D_2^{-it}\otimes I_3)
--    \quad\text{for all }t\in\mathbb R,\
--   &\log D_{123}-(\log D_{12})\otimes I_3
--    =I_1\otimes\log D_{23}-I_1\otimes\log D_2\otimes I_3.
--   \end{aligned}
--   $$
--
--   This gives multiplicative and logarithmic characterizations of strong-subadditivity equality. The smaller densities are constructed from $D_{123}$; their invertibility follows from the hypothesis on the full state.
--
--   **Formalization Note** Registers have order $I\times(J\times K)$. The entropy equality is written with the frozen entropy in bits; multiplication by $\log 2>0$ converts it to the displayed equality in natural units. Powers and logarithms are taken before identity embedding.
-- source:
--   Monotonicity of quantum relative entropy revisited, arXiv:quant-ph/0209053v1, PDF p. 11, Theorem 3: two characterizations of equality in strong subadditivity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P84

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions, inspected at their recorded source locations.

open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower marginalAB)

/-- Petz, arXiv:quant-ph/0209053v1, PDF p.11, Theorem 3.
Every marginal is computed from rho; the only invertibility assumption is on rho.
All smaller-system logarithms/powers are embedded with ordinary identities. -/
theorem equalityInStrongSubadditivity {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K]
    [Nonempty I] [Nonempty J] [Nonempty K]
    (rho : Matrix (I × (J × K)) (I × (J × K)) ℂ)
    (hrho : IsDensityMatrix rho) (hinv : IsUnit rho) :
    let D12 := marginalAB rho
    let D23 := traceLeft rho
    let D2 := traceRight D23
    let eqSSA := vnEntropy rho + vnEntropy D2 = vnEntropy D12 + vnEntropy D23
    (eqSSA ↔ ∀ t : ℝ,
      imaginaryPower rho t * embed12 (K := K) (imaginaryPower D12 (-t)) =
      Matrix.kronecker (1 : Matrix I I ℂ) (imaginaryPower D23 t) *
        Matrix.kronecker (1 : Matrix I I ℂ)
          (Matrix.kronecker (imaginaryPower D2 (-t)) (1 : Matrix K K ℂ))) ∧
    (eqSSA ↔
      cfc Real.log rho - embed12 (K := K) (cfc Real.log D12) =
      Matrix.kronecker (1 : Matrix I I ℂ) (cfc Real.log D23) -
        Matrix.kronecker (1 : Matrix I I ℂ)
          (Matrix.kronecker (cfc Real.log D2) (1 : Matrix K K ℂ))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P84

end
