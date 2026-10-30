-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P48_sts_parametrization
-- name    : QAlgorithms.Papers.Independent.Advance50.P48.sts_parametrization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:04:09.857251+00:00
-- url     : https://prove2.me/theorems/abeffac6-f319-4fc2-9e2f-e46aed5c9f12
-- title:
--   Unnumbered: STS density parametrization and covariance
-- statement:
--   Work on two complete oscillator modes with $[q_j,p_k]=i\delta_{jk}$, vacuum covariance $I/2$, and natural logarithms, with $0\log0=0$. A state is a positive trace-class density of trace one, with no photon cutoff. Write $C_A^G(\rho)$ for the Gaussian discord obtained by measuring mode $B$ and retaining $A$: it is $S(\rho_B)-S(\rho)$ plus the infimum of the actual Born-averaged conditional von Neumann entropy over normalized Gaussian seed POVMs. Exchanging the modes defines $C_B^G$. The entropy $S$ is defined independently on the full oscillator space.
--
--   Let $N_1,N_2,r\ge0$ be finite real numbers, let $\nu(N)$ have number probabilities $N^k/(1+N)^{k+1}$, and let $\rho=S(r)[\nu(N_1)\otimes\nu(N_2)]S(r)^\dagger$, where $S(r)=\exp[r(a^\dagger b^\dagger-ab)]$. Put $N_r=\sinh^2 r$.
--
--   The constructed density is Gaussian with zero first moments and covariance $\sigma=\begin{pmatrix}aI_2&\operatorname{diag}(c,-c)\\\operatorname{diag}(c,-c)&bI_2\end{pmatrix}$, where
--
--   $$a=N_r+\tfrac12+N_1(1+N_r)+N_2N_r,\quad b=N_r+\tfrac12+N_2(1+N_r)+N_1N_r,\quad c=(1+N_1+N_2)\sqrt{N_r(1+N_r)}.$$
--
--   Its smaller and larger symplectic eigenvalues are $\min(N_1+\tfrac12,N_2+\tfrac12)$ and $\max(N_1+\tfrac12,N_2+\tfrac12)$, respectively. These facts identify the moments and spectrum of an actual density, including vacuum and unsqueezed inputs.
-- source:
--   Gaussian quantum discord, arXiv:1003.3207v2, PDF p. 2, Unnumbered: STS density parametrization and covariance

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P48

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsTraceClassChannel IsSeparable productCoeff)

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix coherentMeasure coherentCoefficient)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Frontier30.P04 (modePhase twoModeStandard conditionalCovariance)

open QAlgorithms.Papers.Independent.Frontier30.P14 (partialRight partialLeft)

open QAlgorithms.Papers.Independent.Claimed50.P30 (canonicalOmega)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g thermalProbability)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2: the actual squeezed thermal density has the displayed standard
covariance; its symplectic spectrum follows from the physical squeezing. The
thermal sum's printed Nk is read as Nj for the state nu_j. -/
theorem sts_parametrization (N1 N2 r : ℝ) (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) (hr : 0 ≤ r) :
    GaussianTwo (sts N1 N2 r) 0 (stsCovariance N1 N2 r) ∧
    symplecticMinus (stsCovariance N1 N2 r) = min (N1 + 1/2) (N2 + 1/2) ∧
    symplecticPlus (stsCovariance N1 N2 r) = max (N1 + 1/2) (N2 + 1/2) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P48

end
