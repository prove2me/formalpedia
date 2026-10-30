-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P48_sts_closedDiscord
-- name    : QAlgorithms.Papers.Independent.Advance50.P48.sts_closedDiscord
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:02:42.324894+00:00
-- url     : https://prove2.me/theorems/88f240e3-890f-4cc1-8131-c7742069fd0c
-- title:
--   Main result / Eq. (2): closed Gaussian discord of squeezed thermal states
-- statement:
--   Work on two complete oscillator modes with $[q_j,p_k]=i\delta_{jk}$, vacuum covariance $I/2$, and natural logarithms, with $0\log0=0$. A state is a positive trace-class density of trace one, with no photon cutoff. Write $C_A^G(\rho)$ for the Gaussian discord obtained by measuring mode $B$ and retaining $A$: it is $S(\rho_B)-S(\rho)$ plus the infimum of the actual Born-averaged conditional von Neumann entropy over normalized Gaussian seed POVMs. Exchanging the modes defines $C_B^G$. The entropy $S$ is defined independently on the full oscillator space.
--
--   Let $N_1,N_2,r\ge0$ be finite real numbers, let $\nu(N)$ have number probabilities $N^k/(1+N)^{k+1}$, and let $\rho=S(r)[\nu(N_1)\otimes\nu(N_2)]S(r)^\dagger$, where $S(r)=\exp[r(a^\dagger b^\dagger-ab)]$. Put $N_r=\sinh^2 r$.
--
--   Write the covariance as $\sigma=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$, let $I_1=\det A$, $I_2=\det B$, $I_3=\det C$, $I_4=\det\sigma$, $\Delta=I_1+I_2+2I_3$, and $d_\pm=\sqrt{(\Delta\pm\sqrt{\Delta^2-4I_4})/2}$. Define $h(x)=(x+\tfrac12)\log(x+\tfrac12)-(x-\tfrac12)\log(x-\tfrac12)$. Then
--
--   $$C_A^G(\rho)=h(\sqrt{I_2})-h(d_-)-h(d_+)+h\!\left(\frac{\sqrt{I_1}+2\sqrt{I_1I_2}+2I_3}{1+2\sqrt{I_2}}\right).$$
--
--   The opposite direction is the same expression with $I_1$ and $I_2$ exchanged. This evaluates the independently measurement-defined discord, including product and pure STS.
-- source:
--   Gaussian quantum discord, arXiv:1003.3207v2, PDF p. 3, Main result / Eq. (2): closed Gaussian discord of squeezed thermal states

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

/-- PDF p.3, Eq.(2): the closed Gaussian A-discord of every finite STS, and
its opposite direction by exchanging the two thermal inputs. -/
theorem sts_closedDiscord (N1 N2 r : ℝ) (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) (hr : 0 ≤ r) :
    gaussianDiscordA (sts N1 N2 r) = closedDiscord (stsCovariance N1 N2 r) ∧
    gaussianDiscordA (swapOscillators (sts N1 N2 r)) = closedDiscord (stsCovariance N2 N1 r) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P48

end
