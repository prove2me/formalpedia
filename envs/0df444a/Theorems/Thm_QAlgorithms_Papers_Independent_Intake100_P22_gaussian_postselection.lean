-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_gaussian_postselection
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.gaussian_postselection
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:39:19.306844+00:00
-- url     : https://prove2.me/theorems/42ee4044-2a58-47b8-b7a9-4bc0fe96f3bc
-- title:
--   Normalized Gaussian postselection
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   Let $X$ be a Gaussian operator and $\rho$ a Gaussian density. If $X\rho\ne0$, the normalizing trace is strictly positive and
--   $$
--   \operatorname{Tr}(X\rho X^\dagger)>0,\qquad
--   \rho'=\frac{X\rho X^\dagger}{\operatorname{Tr}(X\rho X^\dagger)}\text{ is a Gaussian density}.
--   $$
--   No full-rank assumption on $\rho$ or nonzero-trace assumption on $X$ is made. This characterizes the conditional state of a possible Gaussian filtering outcome.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 5, Corollary 2: normalized Gaussian postselection

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, Corollary 2: the printed condition is X rho nonzero.
Strict positivity of the normalizing trace is a conclusion. -/
theorem gaussian_postselection {n : ℕ} (s : CARSystem n) (X rho : Op (Qubits n))
    (hX : GaussianOperator s X) (hrho : FermionicGaussianState s rho) (hne : X * rho ≠ 0) :
    0 < (conjSuperop X rho).trace.re ∧
      FermionicGaussianState s (normalizeComplexTrace (conjSuperop X rho)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
