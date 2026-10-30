-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P48_equalEntanglement_differentDiscord
-- name    : QAlgorithms.Papers.Independent.Advance50.P48.equalEntanglement_differentDiscord
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:13:12.221665+00:00
-- url     : https://prove2.me/theorems/68b4e61b-907e-4fb7-9771-51ca45119057
-- title:
--   Unnumbered: equal entanglement and teleportation fidelity can coexist with different discord
-- statement:
--   Work on two complete oscillator modes with $[q_j,p_k]=i\delta_{jk}$, vacuum covariance $I/2$, and natural logarithms, with $0\log0=0$. A state is a positive trace-class density of trace one, with no photon cutoff. Write $C_A^G(\rho)$ for the Gaussian discord obtained by measuring mode $B$ and retaining $A$: it is $S(\rho_B)-S(\rho)$ plus the infimum of the actual Born-averaged conditional von Neumann entropy over normalized Gaussian seed POVMs. Exchanging the modes defines $C_B^G$. The entropy $S$ is defined independently on the full oscillator space.
--
--   For $t>0$ and $0<\mu\le1$ with $2t\sqrt\mu\le1$, let $\rho_{\mu,t}$ be the actual symmetric squeezed thermal state with $N_1=N_2=(\mu^{-1/2}-1)/2$ and $r=-\frac12\log(2t\sqrt\mu)$. Its global purity is $\mu$ and its smallest partially transposed symplectic eigenvalue is $t$. Here purity means $\operatorname{Tr}(\rho^2)$, and total energy $N_T$ means the actual mean total photon occupation.
--
--   There exist $0<t<1/2$ and distinct physical purities $\mu_1,\mu_2$ such that the two actual states $\rho_{\mu_1,t}$ and $\rho_{\mu_2,t}$ are entangled, have their stated actual purities and the same partially transposed symplectic eigenvalue $t$, but
--
--   $$C_A^G(\rho_{\mu_1,t})\ne C_A^G(\rho_{\mu_2,t}),\qquad F_1=F_2=\frac{1}{1+2t}.$$
--
--   Here $F$ is the coherent-state teleportation fidelity in the setting cited by the source. The density-level target is the equal-PT, unequal-discord existence claim; the operational fidelity identification is background. This distinguishes discord from entanglement ordering without relying on the inconsistent rounded thresholds.
-- source:
--   Gaussian quantum discord, arXiv:1003.3207v2, PDF p. 4, Unnumbered: equal entanglement and teleportation fidelity can coexist with different discord

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

/-- PDF p.4: at the same entangled PT level, states with different global
purities can have different Gaussian discord and identical coherent-state
teleportation fidelity. No rounded threshold classification is used. -/
theorem equalEntanglement_differentDiscord :
    ∃ t mu1 mu2 : ℝ, 0 < t ∧ t < 1/2 ∧
      SymmetricDomain mu1 t ∧ SymmetricDomain mu2 t ∧ mu1 ≠ mu2 ∧
      tracePurity (symmetricState mu1 t) = mu1 ∧ tracePurity (symmetricState mu2 t) = mu2 ∧
      ¬ IsSeparable (symmetricState mu1 t) ∧ ¬ IsSeparable (symmetricState mu2 t) ∧
      (∃ V1 V2 : Matrix (modePhase 2) (modePhase 2) ℝ,
        GaussianTwo (symmetricState mu1 t) 0 V1 ∧
        GaussianTwo (symmetricState mu2 t) 0 V2 ∧ ptMinus V1 = t ∧ ptMinus V2 = t ∧
        teleportationFidelity (ptMinus V1) = teleportationFidelity (ptMinus V2)) ∧
      gaussianDiscordA (symmetricState mu1 t) ≠ gaussianDiscordA (symmetricState mu2 t) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P48

end
