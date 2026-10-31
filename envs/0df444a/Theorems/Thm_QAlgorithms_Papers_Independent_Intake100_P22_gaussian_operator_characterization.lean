-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_gaussian_operator_characterization
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.gaussian_operator_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:37:33.332496+00:00
-- url     : https://prove2.me/theorems/c8b75112-c232-46bb-a735-2736223180d1
-- title:
--   Lambda characterization and singular Gaussian normal form
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   Let $X\in\mathcal C_{2n}$, and put $\Lambda=\sum_{a=1}^{2n}c_a\otimes c_a$ in the ordinary two-copy tensor algebra. Then
--   $$
--   X\text{ is Gaussian}\quad\Longleftrightarrow\quad X\text{ is even and }[\Lambda,X\otimes X]=0.
--   $$
--   Moreover, each Gaussian $X$ has $0\le k\le n$, $C\in\mathbb C$, an invertible complex $2n\times2n$ matrix $T$, and a complex skew matrix $M$, with $\mu=T\theta$, such that
--   $$
--   \omega(X,\theta)=C\left(\prod_{a=1}^{2k}\mu_a\right)\exp\!\left(\frac i2\sum_{a,b=2k+1}^{2n}M_{ab}\mu_a\mu_b\right).
--   $$
--   Gaussian operators here are the closure of the nonzero-trace exponential-symbol operators in finite-dimensional topology. The zero operator is included. The two clauses give an intrinsic characterization and a form covering singular operators.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 5, Theorem 1: nonsingular symmetry characterization and singular normal form

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.5-7, Theorem 1: the Lambda characterization and the complete
singular normal form with an even prefix and a general complex GL matrix.
Zero is included by C=0 and k=0; no nonzero-trace hypothesis is imposed. -/
theorem gaussian_operator_characterization {n : ℕ} (s : CARSystem n) (X : Op (Qubits n)) :
    (GaussianOperator s X ↔ InSector s 0 X ∧
      lambdaOp s * Matrix.kronecker X X - Matrix.kronecker X X * lambdaOp s = 0) ∧
    (GaussianOperator s X → ∃ (k : ℕ) (C : ℂ)
      (T M : Matrix (Major n) (Major n) ℂ),
      k ≤ n ∧ T.det ≠ 0 ∧ M.transpose = -M ∧ majoranaSymbol s X = singularForm k C T M) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
