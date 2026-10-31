-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_gaussian_commutes_lambda
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.gaussian_commutes_lambda
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:40:01.851087+00:00
-- url     : https://prove2.me/theorems/bdde860b-f305-4aa2-be44-7e469d89e48b
-- title:
--   Gaussian operators commute with Lambda in two copies
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   Let $X$ be any Gaussian operator, and set $\Lambda=\sum_ac_a\otimes c_a$ using the ordinary tensor product. Then
--   $$
--   [\Lambda,X\otimes X]=0.
--   $$
--   The Gaussian-operator definition includes the finite-dimensional closure of regular operators, hence trace-zero and zero inputs. This is the forward symmetry statement used by Theorem 1.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 6, Lemma 1: Gaussian operators commute with Lambda in two copies

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6, Lemma 1: all Gaussian operators, including singular and zero. -/
theorem gaussian_commutes_lambda {n : ℕ} (s : CARSystem n) (X : Op (Qubits n))
    (hX : GaussianOperator s X) :
    lambdaOp s * Matrix.kronecker X X - Matrix.kronecker X X * lambdaOp s = 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
