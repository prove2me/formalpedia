-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P46_generalized_holevo_convergence
-- name    : QAlgorithms.Papers.Independent.Advance50.P46.generalized_holevo_convergence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:21:38.826407+00:00
-- url     : https://prove2.me/theorems/f6147677-c3c4-44d5-9d69-fd989e764991
-- title:
--   Corollary C.3 (generalized-ensemble Holevo quantity)
-- statement:
--   Let $\mu$ be any trace-norm Borel probability ensemble on $A$, with barycenter $\bar\rho$ of finite mean input energy $E(\mu)>\inf\sigma(H_A)$ for a positive input observable $H_A$. Let $H_B\ge0$ satisfy the Gibbs hypothesis and have spectral-pair exponent $\eta$. For $E>0$ suppose CPTP channels $\Phi,\Psi$ give both output barycenters energy at most $E$, and $\tfrac12\|\Phi-\Psi\|_\diamond^{H_A,E(\mu)}\le\varepsilon$ with $0<\varepsilon<1$. For $0<t\le1/(2\varepsilon)$ and $r=(1+t/2)/(1-\varepsilon t)$,
--
--   $$|\chi(\Phi_*\mu)-\chi(\Psi_*\mu)|\le\varepsilon(2t+r)F_{H_B}\!\left(\frac E{\varepsilon t}\right)+2g(\varepsilon r)+2h(\varepsilon t).$$
--
--   The output Holevo quantities are finite and use genuine relative-entropy integrals, equal to the entropy-difference definition under these output bounds. Neither finite input entropy nor individual signal energy constraints are required. The common high-argument Gibbs remainder recovers the printed expansion of $F_{H_B}$.
-- source:
--   Convergence rates for quantum evolution & entropic continuity bounds in infinite dimensions, arXiv:1810.00863v3, PDF p. 48, Corollary C.3 (generalized-ensemble Holevo quantity)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P46

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P46

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Bridge50.P23 (energyMagnitude numberEnergy)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass traceSize rankOne tensorApply productCoeff IsBarycenter)

attribute [local instance] Classical.propDecidable Classical.decEq

export QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Corollary C.3 (Holevo quantity), PDF p.48. The state rho is the actual
barycenter of the arbitrary Borel ensemble; its finite mean input energy is
used in the ECD norm. Output entropies make the Holevo quantities finite. -/
theorem generalized_holevo_convergence {I J : Type} [Countable I] [Infinite I]
    [Countable J] [Infinite J] (F : Forms.PositiveObservable I)
    (H : Spectral.Hamiltonian J) (hpos : ∀ j, 0 ≤ H.energy j) (hG : H.gibbs)
    (xi : ℝ) (hxi : HasPairRatio H xi) (mu : Ensembles.GeneralizedEnsemble I)
    (Phi Psi : Spectral.Channel I J) (E epsilon : ℝ) (hE : 0 < E)
    (hfinite : borelBarycenterEnergy F mu < ⊤)
    (hEA : formGround F < (borelBarycenterEnergy F mu).toReal)
    (hout : realSpectrumMeanEnergy H.energy (Phi.val (Ensembles.averageCoefficients mu)) ≤
        ENNReal.ofReal E ∧
      realSpectrumMeanEnergy H.energy (Psi.val (Ensembles.averageCoefficients mu)) ≤ ENNReal.ofReal E)
    (heps : 0 < epsilon) (heps1 : epsilon < 1)
    (hdist : energyMagnitude F (borelBarycenterEnergy F mu).toReal
      (fun X => Phi.val X - Psi.val X) ≤ ENNReal.ofReal (2 * epsilon)) :
    ThermalAsymptotic H xi ∧ Ensembles.ensembleHolevo Phi.val mu < ⊤ ∧
      Ensembles.ensembleHolevo Psi.val mu < ⊤ ∧
    ∀ t : ℝ, 0 < t → t ≤ 1 / (2 * epsilon) →
      |(Ensembles.ensembleHolevo Phi.val mu).toReal -
        (Ensembles.ensembleHolevo Psi.val mu).toReal| ≤ holevoModulus H E epsilon t := by sorry

end QAlgorithms.Papers.Independent.Advance50.P46

end
