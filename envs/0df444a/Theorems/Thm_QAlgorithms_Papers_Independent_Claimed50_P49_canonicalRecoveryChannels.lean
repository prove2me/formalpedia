-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P49_canonicalRecoveryChannels
-- name    : QAlgorithms.Papers.Independent.Claimed50.P49.canonicalRecoveryChannels
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:12:20.586715+00:00
-- url     : https://prove2.me/theorems/7c8675d3-8678-419e-87d7-4ea2858bd1a1
-- title:
--   Explicit CPTP connecting channels
-- statement:
--   Use the six canonical forms $A_1,A_2,B_1,B_2,C,D$ of Table 1 on the full one-mode Fock space. Their noise parameter is $N\ge0$; the amplitude $\kappa$ is positive for $C,D$, and $\kappa
--   e1$ for $C$. The $B_1$ noise is fixed to $\operatorname{diag}(0,1/2)$, and $B_2(0)$ is the identity. A physical representation consists of one fixed bounded unitary $U$ on the completed system–environment tensor product and one fixed environment density $\sigma$, independent of the input. Write $E(\rho)=\operatorname{Tr}_B U(\rho\otimes\sigma)U^\dagger$ and $F(\rho)=\operatorname{Tr}_A U(\rho\otimes\sigma)U^\dagger$. Use the Appendix-A canonical dilation and its selected environment, and write $s=N+1/2$. For $A_1,A_2$, the anti-recovery has the original canonical data. For $D$, it has class-$D$ data with amplitude $r=\kappa/\sqrt{\kappa^2+1}$ and noise $(r^2+1)sI$. For $C$ with $\kappa^2\le1/2$, it has $K=rI$, $\alpha=(1-r^2)sI$, where $r=\kappa/\sqrt{1-\kappa^2}$. These maps are CPTP and satisfy
--
--   $$R\circ F=E.$$
--
--   For $B_1$ the weak-recovery has its weak-complement data. For attenuating $C$ with $\kappa^2\ge1/2$, use $r=\sqrt{1-\kappa^2}/\kappa$ and $K=rI$, $\alpha=(1-r^2)sI$. For amplifying $C$, use $r=\sqrt{\kappa^2-1}/\kappa$ and $K=r\sigma_3$, $\alpha=(r^2+1)sI$. These maps are CPTP and satisfy $R\circ E=F$. Every equality holds on all input densities. At $\kappa^2=1/2$, both attenuator recoveries are the identity. This gives the actual connecting maps rather than assuming a recovery identity.
-- source:
--   One-mode Bosonic Gaussian channels: a full weak-degradability classification, arXiv:quant-ph/0609013v2, PDF p. 16, §3.2, bullets

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

/-- Section 3.2, PDF pp.16-17: explicit CPTP connecting maps and their actual
cascade identities. The half-transmissivity recoveries are identity B2, and the
amplifier recovery uses corrected class-D parameters (see weakRecoveryData). -/
theorem canonicalRecoveryChannels (c : CanonicalClass) (k N : ℝ)
    (hvalid : ValidSourceCanonical c k N) (hnotB2 : c ≠ .B2)
    (U : JointUnitary) (hU : ImplementsJointGaussian U (appendixCouplingMatrix c k))
    (sigma : State ℕ) (hsigma : IsThermal sigma.coefficients (environmentNumber c N)) :
    (AntiRegion c k → ∃ R : FockMap,
      IsGaussianChannel R (antiRecoveryData c k N) ∧
      ∀ rho : State ℕ, R (weakComplement U sigma.coefficients rho.coefficients) =
        dilationReceiver U sigma.coefficients rho.coefficients) ∧
    (WeakRegion c k → ∃ R : FockMap,
      IsGaussianChannel R (weakRecoveryData c k N) ∧
      ∀ rho : State ℕ, R (dilationReceiver U sigma.coefficients rho.coefficients) =
        weakComplement U sigma.coefficients rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P49

end
