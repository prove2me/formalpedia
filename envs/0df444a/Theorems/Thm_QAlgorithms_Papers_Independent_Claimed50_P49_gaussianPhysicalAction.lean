-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_gaussianPhysicalAction
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.gaussianPhysicalAction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:04:17.603804+00:00
-- url     : https://prove2.me/theorems/088982dd-8b2e-4785-a16a-7353c7d2e840
-- title:
--   Gaussian receiver action and determinant identity
-- statement:
--   A physical representation consists of one fixed bounded unitary $U$ on the completed system–environment tensor product and one fixed environment density $\sigma$, independent of the input. Write $E(\rho)=\operatorname{Tr}_B U(\rho\otimes\sigma)U^\dagger$ and $F(\rho)=\operatorname{Tr}_A U(\rho\otimes\sigma)U^\dagger$. Take one full Bosonic mode on each leg. Let $\sigma$ be thermal with finite $N\ge0$ and characteristic function $\exp[-(N+1/2)|z|^2/2]$, and let $U$ implement the real symplectic matrix $M=\left(\begin{smallmatrix}m_{11}&m_{21}\\m_{12}&m_{22}\end{smallmatrix}\right)$ in the source row-observable convention. The operational receiver is Gaussian CPTP with
--
--   $$K=m_{11},\quad m=0,\quad\alpha=(N+1/2)m_{12}^Tm_{12},$$
--   $$\det\alpha=(N+1/2)^2(\det m_{12})^2=(N+1/2)^2(\det m_{11}-1)^2\ge\frac{(\det K-1)^2}{4}.$$
--
--   Both the characteristic law and complete positivity are conclusions of this physical representation, including vacuum $N=0$.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 8, (2.12)–(2.13)

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

/-- Equations (2.12)-(2.13), PDF pp.7-8: physical receiver action and CP.
The determinant equality follows from symplecticity, not an extra assumption. -/
theorem gaussianPhysicalAction (U : JointUnitary) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ImplementsJointGaussian U M) (sigma : State ℕ) (N : ℝ)
    (hthermal : IsThermal sigma.coefficients N) :
    IsGaussianChannel (dilationReceiver U sigma.coefficients)
      ⟨couplingBlock M 0 0, (N + 1 / 2) • ((couplingBlock M 1 0).transpose * couplingBlock M 1 0), 0⟩ ∧
    (((N + 1 / 2) • ((couplingBlock M 1 0).transpose * couplingBlock M 1 0) : RealMatrix).det =
      (N + 1 / 2) ^ 2 * (couplingBlock M 1 0).det ^ 2) ∧
    ((N + 1 / 2) ^ 2 * (couplingBlock M 1 0).det ^ 2 =
      (N + 1 / 2) ^ 2 * ((couplingBlock M 0 0).det - 1) ^ 2) ∧
    (((couplingBlock M 0 0).det - 1) / 2) ^ 2 ≤
      ((N + 1 / 2) • ((couplingBlock M 1 0).transpose * couplingBlock M 1 0) : RealMatrix).det := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
