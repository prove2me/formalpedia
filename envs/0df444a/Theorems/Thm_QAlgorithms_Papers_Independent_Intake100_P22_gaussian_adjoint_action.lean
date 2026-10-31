-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_gaussian_adjoint_action
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.gaussian_adjoint_action
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:41:56.950002+00:00
-- url     : https://prove2.me/theorems/14ffef0c-6e85-48ba-8416-b4e217fee59a
-- title:
--   Gaussian adjoint action is a completely positive Gaussian map
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   For any Gaussian operator $X$, define $\mathcal A_X(Y)=XYX^\dagger$ for every operator $Y$. Then
--   $$
--   \mathcal A_X\text{ is both completely positive and a Gaussian linear map}.
--   $$
--   Gaussian map means the integral representation of Definition 3 on all operators, rather than preservation of Gaussian states alone. The claim includes $X=0$ and imposes no trace-preserving condition. It connects Gaussian operator filters to the Lagrangian map calculus.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 1, §I/V/VI: adjoint action of a Gaussian operator is a CP Gaussian map

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.1,5,7,10: adjoint action of a Gaussian operator is a CP Gaussian
map on the full operator algebra, including at X=0. -/
theorem gaussian_adjoint_action {n : ℕ} (s : CARSystem n) (X : Op (Qubits n))
    (hX : GaussianOperator s X) :
    GaussianMap s (conjSuperop X) ∧ LinearCompletelyPositive (conjSuperop X) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
