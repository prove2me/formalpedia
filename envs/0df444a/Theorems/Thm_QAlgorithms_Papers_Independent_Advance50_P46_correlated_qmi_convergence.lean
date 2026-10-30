-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P46_correlated_qmi_convergence
-- name    : QAlgorithms.Papers.Independent.Advance50.P46.correlated_qmi_convergence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:19:31.066787+00:00
-- url     : https://prove2.me/theorems/8fd63200-150a-4a29-9fb0-f33976714919
-- title:
--   Corollary C.1 (QMI)
-- statement:
--   Let $n\ge1$, let $\rho$ be any state on $A^nC$, and let $H_A\ge0$ be an input observable. Set $E_A=\max_k\operatorname{Tr}(H_A\rho_{A_k})<\infty$ and suppose $E_A>\inf\sigma(H_A)$. Let $H_B\ge0$ be Gibbs with spectral-pair exponent $\eta$. Suppose CPTP channels satisfy $\tfrac12\|\Phi-\Psi\|_\diamond^{H_A,E_A}\le\varepsilon$ for $0<\varepsilon<1$ and both output marginal energies are at most $E_k$. Set $E=n^{-1}\sum_kE_k$, $r=(1+t/2)/(1-\varepsilon t)$, with $g$ and $h$ as above. For $0<t<1/(2\varepsilon)$,
--
--   $$|I(B^n:C)_{(\Phi^{\otimes n}\otimes I)(\rho)}-I(B^n:C)_{(\Psi^{\otimes n}\otimes I)(\rho)}|\le2n\varepsilon(2t+r)F_{H_B}\!\left(\frac E{\varepsilon t}\right)+2ng(\varepsilon r)+4nh(\varepsilon t).$$
--
--   Mutual information is relative entropy of the joint state to the product of its marginals and is finite here even for an infinite-entropy reference. The actual correlated tensor action is used. The common Gibbs remainder gives the printed high-argument expansion of $F_{H_B}$.
-- source:
--   Convergence rates for quantum evolution & entropic continuity bounds in infinite dimensions, arXiv:1810.00863v3, PDF p. 47, Corollary C.1 (QMI)

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

/-- Corollary C.1 (QMI), PDF p.47. The actual correlated input and its maximum
marginal energy are used, with strict t<1/(2epsilon). QMI is relative entropy,
so no finite reference entropy is assumed. -/
theorem correlated_qmi_convergence {I J R : Type} [Countable I] [Infinite I]
    [Countable J] [Infinite J] [Countable R] [Infinite R] {n : ℕ} (hn : 1 ≤ n)
    (F : Forms.PositiveObservable I) (H : Spectral.Hamiltonian J)
    (hpos : ∀ j, 0 ≤ H.energy j) (hG : H.gibbs) (xi : ℝ) (hxi : HasPairRatio H xi)
    (Phi Psi : Spectral.Channel I J) (rho : State ((Fin n → I) × R))
    (hfinite : blockInputEnergy F rho < ⊤)
    (hEA : formGround F < (blockInputEnergy F rho).toReal)
    (epsilon : ℝ) (heps : 0 < epsilon) (heps1 : epsilon < 1)
    (hdist : energyMagnitude F (blockInputEnergy F rho).toReal
      (fun X => Phi.val X - Psi.val X) ≤ ENNReal.ofReal (2 * epsilon))
    (energies : Fin n → ℝ)
    (hout : ∀ k : Fin n,
      (realSpectrumMeanEnergy H.energy (Phi.val
        (blockSiteCoefficients k (Spectral.traceSecond rho.coefficients)))).toEReal ≤
          (energies k : EReal) ∧
      (realSpectrumMeanEnergy H.energy (Psi.val
        (blockSiteCoefficients k (Spectral.traceSecond rho.coefficients)))).toEReal ≤
          (energies k : EReal)) :
    ThermalAsymptotic H xi ∧
    QAlgorithms.Papers.Independent.Support50.P18.marginalMutualInformation
      (correlatedOutput Phi rho) < ⊤ ∧
    QAlgorithms.Papers.Independent.Support50.P18.marginalMutualInformation
      (correlatedOutput Psi rho) < ⊤ ∧
    ∀ t : ℝ, 0 < t → t < 1 / (2 * epsilon) →
      |(QAlgorithms.Papers.Independent.Support50.P18.marginalMutualInformation
          (correlatedOutput Phi rho)).toReal -
        (QAlgorithms.Papers.Independent.Support50.P18.marginalMutualInformation
          (correlatedOutput Psi rho)).toReal| ≤
        (n : ℝ) * assistedModulus H ((∑ k, energies k) / (n : ℝ)) epsilon t := by sorry

end QAlgorithms.Papers.Independent.Advance50.P46

end
