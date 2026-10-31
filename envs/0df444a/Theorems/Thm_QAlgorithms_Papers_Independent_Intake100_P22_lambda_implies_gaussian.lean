-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_lambda_implies_gaussian
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.lambda_implies_gaussian
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:41:03.818436+00:00
-- url     : https://prove2.me/theorems/976179f3-0dda-4ab0-945f-9c3e7f927a38
-- title:
--   Converse Lambda characterization including singular inputs
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   For an even operator $X\in\mathcal C_{2n}$, with $\Lambda=\sum_ac_a\otimes c_a$ in the ordinary tensor algebra,
--   $$
--   [\Lambda,X\otimes X]=0\quad\Longrightarrow\quad X\text{ is Gaussian}.
--   $$
--   The conclusion uses the closure definition of Gaussian operators, and the hypothesis does not require nonzero trace. This includes the singular part of the symmetry characterization.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 6, Lemma 2: converse Lambda characterization

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.6-7, Lemma 2: the singular case is part of the converse. -/
theorem lambda_implies_gaussian {n : ℕ} (s : CARSystem n) (X : Op (Qubits n))
    (heven : InSector s 0 X)
    (hcomm : lambdaOp s * Matrix.kronecker X X - Matrix.kronecker X X * lambdaOp s = 0) :
    GaussianOperator s X := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
