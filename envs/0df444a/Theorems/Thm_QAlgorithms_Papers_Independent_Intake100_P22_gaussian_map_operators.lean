-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_gaussian_map_operators
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.gaussian_map_operators
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:44:10.979869+00:00
-- url     : https://prove2.me/theorems/a1c8d4b8-06ac-47b2-b5a2-737416bb5a7a
-- title:
--   Gaussian maps preserve all Gaussian operators
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   For every Gaussian linear map $E$ and every Gaussian operator $X$,
--   $$
--   E(X)\text{ is a Gaussian operator}.
--   $$
--   Both the input and output use the closure definition, including singular and zero operators. The output is not asserted to be a normalized density for a general complex Gaussian map. This is the closure property underlying the covariance update formulas.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 8, Lemma 4: Gaussian maps preserve all Gaussian operators

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, Lemma 4: Gaussian operators, rather than only normalized states,
are preserved, including trace-zero outputs. -/
theorem gaussian_map_operators {n : ℕ} (s : CARSystem n)
    (E : Superop (Qubits n) (Qubits n)) (hE : GaussianMap s E)
    (X : Op (Qubits n)) (hX : GaussianOperator s X) :
    GaussianOperator s (E X) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
