-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P27_thermalRateAndOrbitEnergy
-- name    : QAlgorithms.Papers.Independent.Next46.P27.thermalRateAndOrbitEnergy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:27:57.954059+00:00
-- url     : https://prove2.me/theorems/a650c905-f704-4f8b-b61a-751454535f56
-- title:
--   Local thermal rate minimum and orbit-energy minima
-- statement:
--   Let $\beta>0$, $\gamma>0$, and let $\rho_\beta$ be the full Gibbs density. Its finite input entropy is fixed. For the lower right Dini entropy-production rate $R_\gamma$, there exists $r>0$ such that every density $X$ with the same entropy and $\|X-\rho_\beta\|_1<r$ satisfies
--
--   $$R_\gamma(\rho_\beta)\le R_\gamma(X).$$
--
--   Write $\rho_{\beta,\alpha}=D(\alpha)\rho_\beta D(\alpha)^\dagger$, and use the extended mean photon number $E(X)=\sum_j j\langle j|X|j\rangle\in[0,+\infty]$. For every $\alpha\in\mathbb C$ and every $v\ge0$,
--
--   $$E(\rho_\beta)\le E(\rho_{\beta,\alpha}),\qquad E(\Phi_v(\rho_\beta))\le E(\Phi_v(\rho_{\beta,\alpha})).$$
--
--   Thus the thermal representative minimizes energy along its displacement orbit, both before and after thermalization. The rate minimum is local; no assertion is made about energy attainment on other connected components.
-- source:
--   The bosonic minimum output entropy conjecture and Lagrangian minimization, arXiv:0906.2758v3, PDF p. 4, Section VI: local entropy-rate and orbit-energy minima

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P27

open Filter MeasureTheory

open scoped Topology ENNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

-- Mathlib deliberately leaves the general C*-algebra calculus opt-in.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- PDF p.4, Section VI: local entropy-rate minimum at fixed positive input
entropy, and minimum energy in its displacement orbit. Energy is extended so
no infinite-moment input is assigned a real tsum default. -/
theorem thermalRateAndOrbitEnergy (beta gamma : ℝ) (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    FixedEntropyLocalMinimum (entropyRate gamma) (A.photonMeanThermalState (gibbsMean beta)) ∧
    (∀ alpha : ℂ, energy (A.photonMeanThermalState (gibbsMean beta)) ≤ energy (orbitPoint (A.photonMeanThermalState (gibbsMean beta)) alpha)) ∧
    ∀ v : ℝ, 0 ≤ v → ∀ alpha : ℂ,
      energy (A.displacementNoiseChannel v (A.photonMeanThermalState (gibbsMean beta))) ≤
        energy (A.displacementNoiseChannel v (orbitPoint (A.photonMeanThermalState (gibbsMean beta)) alpha)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P27

end
