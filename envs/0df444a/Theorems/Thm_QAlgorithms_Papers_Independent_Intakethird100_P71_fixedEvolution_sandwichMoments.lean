-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P71_fixedEvolution_sandwichMoments
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P71.fixedEvolution_sandwichMoments
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:04:49.857563+00:00
-- url     : https://prove2.me/theorems/7a35e11e-8378-40d2-8d14-a679e5f30994
-- title:
--   Fixed-evolution sandwich has the required local moments
-- statement:
--   Fix $N$ qudits, $d\ge2$, and an arbitrary unitary $U_0$ independently of the unknown input state. Let $L$ and $R$ be independent random local unitaries whose twirling superoperators equal those of normalized product Haar measure at orders two and three. For the sandwich $U=L U_0 R$, choose the prior basis outcome $b$ uniformly and set $S=U^\dagger|b\rangle\langle b|U$. Its prior law $\nu$ is a probability measure with integrable polynomial moments. If $\nu^{\rm LS}$ is its local Haar twirl, then
--
--   $$\mathbb E_\nu S^{\otimes t}=\mathbb E_{\nu^{\rm LS}}S^{\otimes t},\qquad t\in\{2,3\}.$$
--
--   When its measurement channel is injective, Eq. (12) has unique real coefficients defining its inverse, and the resulting shadows reconstruct every density matrix without bias. This formulation includes the moment property used for Clifford end factors without asserting continuous Haar invariance of their discrete probability laws.
-- source:
--   Classical Shadow Tomography with Locally Scrambled Quantum Dynamics, arXiv:2107.04817v4, PDF p. 11, §III C: fixed evolution sandwiched by local random unitaries

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P71

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Intakethird100.P71

attribute [local instance] Classical.propDecidable

local notation "Config" n:max d:max =>
  QAlgorithms.Papers.Independent.Information100.P21.Config (P := Fin n) (fun _ => d)

local notation "Op" n:max d:max =>
  QAlgorithms.Papers.Independent.Information100.P21.Op (Config n d)

attribute [local instance] QAlgorithms.Papers.Independent.Intakethird100.P71.matrixContinuousENorm

local notation "Unitary" n:max d:max => Matrix.unitaryGroup (Config n d) ℂ

local notation "Local" n:max d:max => Fin n → Matrix.unitaryGroup (Fin d) ℂ

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF p.11 §III C: fixed evolution sandwiched between independent local
2/3-designs has the required snapshot moments. Finite Clifford factors are not
asserted Haar-invariant as laws. Completeness is needed only for reconstruction. -/
theorem fixedEvolution_sandwichMoments {n d : ℕ} (hd : 2 ≤ d) (U0 : Unitary n d)
    (H muL muR : Measure (Local n d)) [IsProbabilityMeasure H] [H.IsMulLeftInvariant]
    [IsProbabilityMeasure muL] [IsProbabilityMeasure muR]
    (hL : ∀ t ∈ ({2,3} : Finset ℕ), IsLocalDesign muL H t)
    (hR : ∀ t ∈ ({2,3} : Finset ℕ), IsLocalDesign muR H t) :
    let nu := sandwichPrior U0 muL muR
    IsProbabilityMeasure nu ∧ SnapshotPolynomialIntegrable nu ∧
    (∀ t ∈ ({2,3} : Finset ℕ), snapshotMoment nu t = snapshotMoment (twirled H nu) t) ∧
    (∀ hc : Complete nu, ∃! r : Finset (Fin n) → ℝ,
      CoefficientSystem nu r ∧ (∀ X : Op n d, efReconstruct r X = snapshotInverse nu hc X) ∧
      (∀ rho : Op n d, IsDensityMatrix rho →
        (∫ S, efReconstruct r S ∂posteriorOf nu rho) = rho)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P71

end
