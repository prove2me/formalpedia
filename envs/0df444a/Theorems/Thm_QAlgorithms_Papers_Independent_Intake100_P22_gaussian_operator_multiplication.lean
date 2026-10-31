-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_gaussian_operator_multiplication
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.gaussian_operator_multiplication
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:38:23.128387+00:00
-- url     : https://prove2.me/theorems/5a02a53d-ee4c-485f-aea0-7c87dfd0e6fe
-- title:
--   Closure under operator multiplication
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   If $X,Y\in\mathcal C_{2n}$ are Gaussian operators, including possibly trace-zero operators, then
--   $$
--   XY\text{ is a Gaussian operator}.
--   $$
--   Gaussianity uses the finite-dimensional closure of regular exponential symbols. The product is multiplication in the operator algebra. This gives closure of Gaussian transformations under successive operator applications.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 5, Corollary 1: multiplication closure

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, Corollary 1: operator multiplication, not symbol multiplication. -/
theorem gaussian_operator_multiplication {n : ℕ} (s : CARSystem n) (X Y : Op (Qubits n))
    (hX : GaussianOperator s X) (hY : GaussianOperator s Y) :
    GaussianOperator s (X * Y) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
