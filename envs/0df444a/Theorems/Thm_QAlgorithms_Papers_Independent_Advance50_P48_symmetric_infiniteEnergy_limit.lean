-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P48_symmetric_infiniteEnergy_limit
-- name    : QAlgorithms.Papers.Independent.Advance50.P48.symmetric_infiniteEnergy_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:11:47.246527+00:00
-- url     : https://prove2.me/theorems/c85473aa-be0e-4af6-a5a0-93278d9ded82
-- title:
--   Unnumbered: fixed-PT infinite-energy limit of symmetric STS discord
-- statement:
--   Work on two complete oscillator modes with $[q_j,p_k]=i\delta_{jk}$, vacuum covariance $I/2$, and natural logarithms, with $0\log0=0$. A state is a positive trace-class density of trace one, with no photon cutoff. Write $C_A^G(\rho)$ for the Gaussian discord obtained by measuring mode $B$ and retaining $A$: it is $S(\rho_B)-S(\rho)$ plus the infimum of the actual Born-averaged conditional von Neumann entropy over normalized Gaussian seed POVMs. Exchanging the modes defines $C_B^G$. The entropy $S$ is defined independently on the full oscillator space.
--
--   For $t>0$ and $0<\mu\le1$ with $2t\sqrt\mu\le1$, let $\rho_{\mu,t}$ be the actual symmetric squeezed thermal state with $N_1=N_2=(\mu^{-1/2}-1)/2$ and $r=-\frac12\log(2t\sqrt\mu)$. Its global purity is $\mu$ and its smallest partially transposed symplectic eigenvalue is $t$. Here purity means $\operatorname{Tr}(\rho^2)$, and total energy $N_T$ means the actual mean total photon occupation.
--
--   For every fixed $t>0$, both directions agree on this symmetric family, every physical approximant has finite energy, and
--
--   $$\lim_{\mu\to0^+}C_A^G(\rho_{\mu,t})=(1+2t)\log\!\left(\frac{1+2t}{2t}\right)-1,\qquad N_T(\rho_{\mu,t})\longrightarrow+\infty.$$
--
--   The limit is taken through eventually physical positive purities; no infinite-energy density is introduced. At $t=1/2$ the discord limit is $2\log2-1$. This supplies the finite-state asymptotic interpretation of the source expression.
-- source:
--   Gaussian quantum discord, arXiv:1003.3207v2, PDF p. 3, Unnumbered: fixed-PT infinite-energy limit of symmetric STS discord

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

/-- PDF p.3: every fixed t>0 has the stated one-sided infinite-energy limit.
The simplified constant equals the printed expression despite mismatched brackets. -/
theorem symmetric_infiniteEnergy_limit (t : ℝ) (ht : 0 < t) :
    (∀ mu : ℝ, SymmetricDomain mu t →
      gaussianDiscordA (swapOscillators (symmetricState mu t)) = gaussianDiscordA (symmetricState mu t) ∧
      totalPhotonEnergy (symmetricState mu t) < ⊤) ∧
    Tendsto (fun mu : ℝ => gaussianDiscordA (symmetricState mu t)) (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (infiniteEnergyDiscord t)) ∧
    Tendsto (fun mu : ℝ => (totalPhotonEnergy (symmetricState mu t)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by sorry

end QAlgorithms.Papers.Independent.Advance50.P48

end
