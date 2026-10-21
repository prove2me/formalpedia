-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_gaussianWeakComplement
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.gaussianWeakComplement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:11:01.685649+00:00
-- url     : https://prove2.me/theorems/3fd595a5-e2d7-4bd2-82ad-5ad5ccf07b2c
-- title:
--   Gaussian operational weak complement
-- statement:
--   A physical representation consists of one fixed bounded unitary $U$ on the completed system–environment tensor product and one fixed environment density $\sigma$, independent of the input. Write $E(\rho)=\operatorname{Tr}_B U(\rho\otimes\sigma)U^\dagger$ and $F(\rho)=\operatorname{Tr}_A U(\rho\otimes\sigma)U^\dagger$. Take one full input Bosonic mode and one environmental mode. Suppose $U$ implements the real symplectic matrix $M=\left(\begin{smallmatrix}m_{11}&m_{21}\\m_{12}&m_{22}\end{smallmatrix}\right)$, and $\sigma$ is thermal with finite $N\ge0$ and source characteristic function $\exp[-(N+1/2)|z|^2/2]$. Then the operational weak complement is Gaussian CPTP and, for every input density,
--
--   $$\chi_{F(\rho)}(z)=\chi_\rho(m_{21}z)\exp[-(N+1/2)|m_{22}z|^2/2].$$
--
--   Its data are $\widetilde K=m_{21}$, $\widetilde\alpha=(N+1/2)m_{22}^Tm_{22}$ and $\widetilde m=0$, satisfying the one-mode CP condition. This is the one-mode thermal result actually proved by this source, not an arbitrary multimode covariance theorem.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 15, §3.1; (3.1)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P49

noncomputable section

open scoped BigOperators ENNReal Topology

open Filter MeasureTheory

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

namespace QAlgorithms.Papers.Independent.Claimed50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Equation (3.1), PDF pp.14-15: operational environmental leg, one full input
mode and one full output mode. Printed intermediate Tr_b(rho_a ...) is corrected
to the type-correct carrier pairing; CP is a conclusion, not a hypothesis.
This source does not state the provisional arbitrary-multimode dependency claim. -/
theorem gaussianWeakComplement (U : JointUnitary) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ImplementsJointGaussian U M) (sigma : State ℕ) (N : ℝ)
    (hthermal : IsThermal sigma.coefficients N) :
    IsGaussianChannel (weakComplement U sigma.coefficients)
      ⟨couplingBlock M 0 1, (N + 1 / 2) • ((couplingBlock M 1 1).transpose * couplingBlock M 1 1), 0⟩ := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
