-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_canonicalSingleModeDilations
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.canonicalSingleModeDilations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:07:54.844778+00:00
-- url     : https://prove2.me/theorems/caf94a8b-a4ea-4a71-98ce-7bfd50e2683c
-- title:
--   Concrete single-mode canonical dilations
-- statement:
--   Use the six canonical forms $A_1,A_2,B_1,B_2,C,D$ of Table 1 on the full one-mode Fock space. Their noise parameter is $N\ge0$; the amplitude $\kappa$ is positive for $C,D$, and $\kappa
--   e1$ for $C$. The $B_1$ noise is fixed to $\operatorname{diag}(0,1/2)$, and $B_2(0)$ is the identity. For every valid canonical form other than $B_2$, there exist a bounded unitary $U$ implementing the exact matrix $M_c(\kappa)$ printed in Appendix A and a thermal density $\sigma$ on one external full Bosonic mode, such that
--
--   $$E(\rho)=\operatorname{Tr}_B U(\rho\otimes\sigma)U^\dagger\quad\text{has the canonical data of }c.$$
--
--   The environment parameter is zero for $B_1$ and equals $N$ for $A_1,A_2,C,D$. The chosen environment is pure exactly when this parameter is zero. The complete matrices, including the environmental output axes, are those fixed in Appendix A. Existence of the implementer is a conclusion, making the representations available for the subsequent weak-complement construction.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 11, §2.4; Appendix A

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

/-- Section 2.4 and Appendix A, PDF pp.11-13,20: the explicit symplectic
implementer and thermal state EXIST; implementation is never a hypothesis
replacing this construction. B1 is vacuum; the other pure cases are N0=0. -/
theorem canonicalSingleModeDilations (c : CanonicalClass) (k N : ℝ)
    (hvalid : ValidSourceCanonical c k N) (hnotB2 : c ≠ .B2) :
    ∃ (U : JointUnitary) (sigma : State ℕ),
      ImplementsJointGaussian U (appendixCouplingMatrix c k) ∧
      IsThermal sigma.coefficients (environmentNumber c N) ∧
      IsGaussianChannel (dilationReceiver U sigma.coefficients) (canonicalData c k N) ∧
      (PureDensity sigma.coefficients ↔ environmentNumber c N = 0) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
