-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P16_dephasingThermalOptimizer
-- name    : QAlgorithms.Papers.Independent.Bridge50.P16.dephasingThermalOptimizer
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:41:16.686558+00:00
-- url     : https://prove2.me/theorems/c701e5f1-c83e-4dff-b64e-2813336aacc1
-- title:
--   Theorem 9 proof-supported correction: dephasing and thermal optimizer
-- statement:
--   Let $1/2\le\eta\le1$, $E\ge0$, and let $\rho$ be a normalized positive trace-class oscillator state with finite mean photon number at most $E$. Let $\Delta(\rho)$ denote its complete Fock-basis dephasing, $\theta_E$ the thermal state of mean $E$, and $I_c(\rho,\mathcal N_\eta)=H_2(\mathcal N[\eta,0](\rho))-H_2(\mathcal N[1-\eta,0](\rho))$, where $H_2$ is von Neumann entropy in bits. The displayed output entropies for $\rho$, $\Delta(\rho)$ and $\theta_E$ are finite, and
--
--   $$I_c(\rho,\mathcal N_\eta)\le I_c(\Delta(\rho),\mathcal N_\eta),\qquad I_c(\rho,\mathcal N_\eta)\le I_c(\theta_E,\mathcal N_\eta)=g(\eta E)-g((1-\eta)E),$$
--
--   where $g(x)=(x+1)\log_2(x+1)-x\log_2x$, with $0\log_2 0=0$. Dephasing preserves a normalized finite-energy state. This is the proof-supported optimizer statement in the degradable regime.
-- source:
--   Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes, arXiv:1801.07271v2, PDF p. 5, Theorem 9 proof-supported correction: dephasing and thermal optimizer

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P16

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P16

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P32 (CPTP applyChoi)

/-- Theorem 9 proof-supported correction, PDF pp.4--5 Eqs.(19)--(22).
Printed: Eq.(18) asserts eta in [0,1]. Changed: eta>=1/2, finite input energy.
Why: the proof uses concavity from degradability; at eta=0 dephasing a pure
(|0>+|1>)/sqrt(2) decreases Ic from 0 to -1. Finiteness is concluded explicitly.
The Gaussian optimizer theorem [14] is background, not a hypothesis on X. -/
theorem dephasingThermalOptimizer (eta budget : ℝ)
    (h0 : (1 / 2 : ℝ) ≤ eta) (h1 : eta ≤ 1) (hbudget : 0 ≤ budget)
    (X : B.FockOperator) (hX : B.IsDensity X) (hfinite : C.FiniteEnergy X)
    (henergy : (∑' j : ℕ, (j : ℝ) * (X (B.fockKet j) j).re) ≤ budget) :
    B.HasFockMatrix (dephasedOperator X)
      (QAlgorithms.Papers.Independent.Information100.P51.fockDephasing (operatorCoeff X)) ∧
    B.IsDensity (dephasedOperator X) ∧ C.FiniteEnergy (dephasedOperator X) ∧
    B.ThermalRealized (2 * budget + 1) ∧
    (∀ Y ∈ ({X, dephasedOperator X, C.photonMeanThermalState budget} : Set B.FockOperator),
      (C.fockEntropyNats (C.thermal eta 0 Y) / ENNReal.ofReal (Real.log 2)) ≠ ⊤ ∧
        (C.fockEntropyNats (C.thermal (1 - eta) 0 Y) / ENNReal.ofReal (Real.log 2)) ≠ ⊤) ∧
    pureLossIc eta X ≤ pureLossIc eta (dephasedOperator X) ∧
    pureLossIc eta X ≤ pureLossIc eta (C.photonMeanThermalState budget) ∧
    pureLossIc eta (C.photonMeanThermalState budget) =
      thermalEntropyBits (eta * budget) - thermalEntropyBits ((1 - eta) * budget) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P16

end
