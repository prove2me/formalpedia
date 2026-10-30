-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P48_symmetric_separable_purity
-- name    : QAlgorithms.Papers.Independent.Advance50.P48.symmetric_separable_purity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:10:36.662288+00:00
-- url     : https://prove2.me/theorems/68568b05-8cb7-4fb9-8715-b8a9dc4b3c7c
-- title:
--   Unnumbered / Fig.2a: separable symmetric STS at fixed PT eigenvalue
-- statement:
--   Work on two complete oscillator modes with $[q_j,p_k]=i\delta_{jk}$, vacuum covariance $I/2$, and natural logarithms, with $0\log0=0$. A state is a positive trace-class density of trace one, with no photon cutoff. Write $C_A^G(\rho)$ for the Gaussian discord obtained by measuring mode $B$ and retaining $A$: it is $S(\rho_B)-S(\rho)$ plus the infimum of the actual Born-averaged conditional von Neumann entropy over normalized Gaussian seed POVMs. Exchanging the modes defines $C_B^G$. The entropy $S$ is defined independently on the full oscillator space.
--
--   For $t>0$ and $0<\mu\le1$ with $2t\sqrt\mu\le1$, let $\rho_{\mu,t}$ be the actual symmetric squeezed thermal state with $N_1=N_2=(\mu^{-1/2}-1)/2$ and $r=-\frac12\log(2t\sqrt\mu)$. Its global purity is $\mu$ and its smallest partially transposed symplectic eigenvalue is $t$. Here purity means $\operatorname{Tr}(\rho^2)$, and total energy $N_T$ means the actual mean total photon occupation.
--
--   Fix $t\ge1/2$. For two distinct physical purities $0<\mu_1<\mu_2\le\min(1,(4t^2)^{-1})$, both states are separable and
--
--   $$C_A^G(\rho_{\mu_2,t})<C_A^G(\rho_{\mu_1,t}),\qquad N_T(\mu,t)=t-1+\frac{1}{4t\mu},\qquad N_T(\mu_2,t)<N_T(\mu_1,t).$$
--
--   Thus discord strictly increases with total energy along this fixed-PT family. The physical endpoint is part of the assertion; for $t\ge1/2$, purity one is permitted only at $t=1/2$. This makes the source monotonicity a quantified comparison on physical densities.
-- source:
--   Gaussian quantum discord, arXiv:1003.3207v2, PDF p. 3, Unnumbered / Fig.2a: separable symmetric STS at fixed PT eigenvalue

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

/-- PDF p.3, Fig.2a: fixed t>=1/2, ordered DISTINCT physical purities.
Decreasing purity strictly increases discord and total energy. The physical
upper purity endpoint depends on t; mu=1 requires t=1/2 in this regime. -/
theorem symmetric_separable_purity (t mu1 mu2 : ℝ) (ht : 1/2 ≤ t)
    (hm1 : SymmetricDomain mu1 t) (hm2 : SymmetricDomain mu2 t) (hmu : mu1 < mu2) :
    tracePurity (symmetricState mu1 t) = mu1 ∧ tracePurity (symmetricState mu2 t) = mu2 ∧
    IsSeparable (symmetricState mu1 t) ∧ IsSeparable (symmetricState mu2 t) ∧
    gaussianDiscordA (symmetricState mu2 t) < gaussianDiscordA (symmetricState mu1 t) ∧
    totalPhotonEnergy (symmetricState mu1 t) = ENNReal.ofReal (t - 1 + (4*t*mu1)⁻¹) ∧
    totalPhotonEnergy (symmetricState mu2 t) = ENNReal.ofReal (t - 1 + (4*t*mu2)⁻¹) ∧
    totalPhotonEnergy (symmetricState mu2 t) < totalPhotonEnergy (symmetricState mu1 t) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P48

end
