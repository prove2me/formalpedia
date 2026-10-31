-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_gaussian_state_spectrum
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.gaussian_state_spectrum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:35:47.721646+00:00
-- url     : https://prove2.me/theorems/ec013f0e-ddae-4ec1-8df0-8460c1200d1c
-- title:
--   Gaussian product form, realizable covariances, and purity
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   Every Gaussian density $\rho$ is canonically conjugate to a product with real parameters $\lambda_j\in[-1,1]$:
--   $$
--   V\rho V^\dagger=2^{-n}\prod_{j=1}^n(I+i\lambda_jc_{2j-1}c_{2j}).
--   $$
--   A real skew matrix $M$ is the covariance of a Gaussian density if and only if $M^TM\le I$ in positive-semidefinite order. For every Gaussian density with covariance $M$, purity is characterized by
--   $$
--   \rho^2=\rho\quad\Longleftrightarrow\quad M^TM=I\quad\Longleftrightarrow\quad\lambda_j\in\{-1,1\}\ \text{for all }j.
--   $$
--   The canonical conjugation uses the Hamiltonians of Eq.(4); signed parameters are allowed. These statements include mixed, rank-deficient, and zero-mode densities.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 4, §IV, Eqs.(18)–(19): Gaussian-state normal form, realizable covariance and purity

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Eqs.(18)-(19): canonical product form, both directions of
covariance realizability, and equivalent purity criteria, including n=0. -/
theorem gaussian_state_spectrum {n : ℕ} (s : CARSystem n) :
    (∀ rho M, StateWith s rho M →
      ∃ (lambda : Fin n → ℝ) (V : Op (Qubits n)), IsCanonicalFLO s V ∧
        (∀ j, -1 ≤ lambda j ∧ lambda j ≤ 1) ∧
        conjSuperop V rho = productState s lambda ∧
        ((rho * rho = rho) ↔ ∀ j, lambda j = -1 ∨ lambda j = 1)) ∧
    (∀ M : Matrix (Major n) (Major n) ℝ, M.transpose = -M →
      ((∃ rho : Op (Qubits n), StateWith s rho M) ↔
        (1 - (M.map Complex.ofReal).transpose * M.map Complex.ofReal).PosSemidef)) ∧
    (∀ rho M, StateWith s rho M →
      ((rho * rho = rho) ↔ (M.map Complex.ofReal).transpose * M.map Complex.ofReal = 1)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
