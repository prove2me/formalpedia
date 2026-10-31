-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_bistochasticity_criterion
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.bistochasticity_criterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:46:25.649023+00:00
-- url     : https://prove2.me/theorems/84021fd4-1b2b-46ba-ab35-96ec226e914b
-- title:
--   Bistochasticity criterion and homogeneous covariance action
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   A map is bistochastic here when it is trace preserving on all operators and satisfies $E(I)=I$. For a Gaussian map with parameters $(A,B,D,C)$,
--   $$
--   E\text{ is bistochastic}\quad\Longleftrightarrow\quad A=D=0,\ C=1.
--   $$
--   For every regular Gaussian input with complex covariance $M$, the output is regular and its covariance is
--   $$
--   M'=BMB^T.
--   $$
--   No complete-positivity hypothesis is part of this statement. The result identifies exactly when the affine covariance term disappears.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 9, §VI: bistochasticity criterion and homogeneous covariance action

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9: bistochasticity is TP plus unitality; CP is not assumed. -/
theorem bistochasticity_criterion {n : ℕ} (s : CARSystem n)
    (E : Superop (Qubits n) (Qubits n)) (K : GrassmannKernel n) (hE : HasGrassmannKernel s E K) :
    (Bistochastic E ↔ K.A = 0 ∧ K.D = 0 ∧ K.C = 1) ∧
    (Bistochastic E → ∀ X M, RegularWith s X M →
      RegularWith s (E X) (K.B * M * K.B.transpose) ∧
        regularCorrelation s (E X) = K.B * M * K.B.transpose) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
