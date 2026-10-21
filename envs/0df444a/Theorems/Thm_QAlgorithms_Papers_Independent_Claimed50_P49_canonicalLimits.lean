-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_canonicalLimits
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.canonicalLimits
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:10:06.238473+00:00
-- url     : https://prove2.me/theorems/7e85c755-654c-485e-b056-56ca68e3793b
-- title:
--   Canonical pointwise characteristic limits
-- statement:
--   Use the six canonical forms $A_1,A_2,B_1,B_2,C,D$ of Table 1 on the full one-mode Fock space. Their noise parameter is $N\ge0$; the amplitude $\kappa$ is positive for $C,D$, and $\kappa
--   e1$ for $C$. The $B_1$ noise is fixed to $\operatorname{diag}(0,1/2)$, and $B_2(0)$ is the identity. Convergence below means pointwise convergence of output characteristic functions for every fixed input density and every Weyl argument. For $N>0$, as $\kappa\to1$ through positive $\kappa
--   e1$, use class $C$ with
--
--   $$N^{\prime}=\frac{N}{|\kappa^2-1|}-\frac12,\qquad K=\kappa I,\qquad\alpha=NI.$$
--
--   Eventually $N^{\prime}\ge0$, these data have actual single-mode thermal dilations which are weakly degradable, and they converge to $B_2(N)$. For $N=0$, vacuum attenuators with $0<\kappa<1$ tending to one are eventually weakly degradable and converge to the identity. For fixed $N\ge0$, either canonical $C$ or $D$ tends to $A_1(N)$ as $\kappa\to0^+$, with eventual valid parameters. These statements specify the source characteristic-function limits without choosing a stronger channel norm.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 10, §2.3; §2.5; §3.2

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

/-- Sections 2.3,2.5,3.2, PDF pp.10-11,14,17: pointwise sourceCharacteristic
limits, with eventual valid thermal parameters and actual weakly degradable
approximants. No diamond-norm or quantum-capacity continuity is asserted. -/
theorem canonicalLimits :
    (∀ (N : ℝ), 0 < N →
      (∀ (rho : State ℕ) z,
        Tendsto (fun k : ℝ => gaussianTransform (nearB2Data N k) (sourceCharacteristic rho.coefficients) z)
          (nhdsWithin 1 {k : ℝ | 0 < k ∧ k ≠ 1})
          (nhds (gaussianTransform (canonicalData .B2 0 N) (sourceCharacteristic rho.coefficients) z))) ∧
      (∀ᶠ k : ℝ in nhdsWithin 1 {k : ℝ | 0 < k ∧ k ≠ 1},
        0 ≤ N / |k ^ 2 - 1| - 1 / 2 ∧
        nearB2Data N k = canonicalData .C k (N / |k ^ 2 - 1| - 1 / 2) ∧
        ∃ (U : JointUnitary) (sigma : State ℕ),
          ImplementsJointGaussian U (appendixCouplingMatrix .C k) ∧
          IsThermal sigma.coefficients (N / |k ^ 2 - 1| - 1 / 2) ∧
          IsGaussianChannel (dilationReceiver U sigma.coefficients) (nearB2Data N k) ∧
          WeaklyDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients))) ∧
    ((∀ (rho : State ℕ) z,
      Tendsto (fun k : ℝ => gaussianTransform (canonicalData .C k 0) (sourceCharacteristic rho.coefficients) z)
        (nhdsWithin 1 (Set.Ioo 0 1)) (nhds (sourceCharacteristic rho.coefficients z))) ∧
      (∀ᶠ k : ℝ in nhdsWithin 1 (Set.Ioo 0 1),
        ∃ (U : JointUnitary) (sigma : State ℕ),
          ImplementsJointGaussian U (appendixCouplingMatrix .C k) ∧ IsThermal sigma.coefficients 0 ∧
          IsGaussianChannel (dilationReceiver U sigma.coefficients) (canonicalData .C k 0) ∧
          WeaklyDegradable (dilationReceiver U sigma.coefficients) (weakComplement U sigma.coefficients))) ∧
    (∀ (N : ℝ), 0 ≤ N → ∀ c ∈ ({CanonicalClass.C, CanonicalClass.D} : Set CanonicalClass),
      (∀ᶠ k : ℝ in nhdsWithin 0 (Set.Ioi 0), ValidSourceCanonical c k N) ∧
      ∀ (rho : State ℕ) z,
        Tendsto (fun k : ℝ => gaussianTransform (canonicalData c k N) (sourceCharacteristic rho.coefficients) z)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (gaussianTransform (canonicalData .A1 0 N) (sourceCharacteristic rho.coefficients) z))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
