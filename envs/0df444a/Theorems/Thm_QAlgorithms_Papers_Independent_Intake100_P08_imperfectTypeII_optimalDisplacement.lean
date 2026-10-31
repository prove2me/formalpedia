-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P08_imperfectTypeII_optimalDisplacement
-- name    : QAlgorithms.Papers.Independent.Intake100.P08.imperfectTypeII_optimalDisplacement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:50:16.209994+00:00
-- url     : https://prove2.me/theorems/3528e7b4-6269-4229-95f1-a0c389989083
-- title:
--   Mode mismatch: Poisson error law and corrected optimal displacement condition
-- statement:
--   Let $|\pm\alpha\rangle$ be equiprobable coherent signals with known $\alpha\ge0$. Fix $0\le\eta,\tau,\xi\le1$ and $\nu\ge0$, denoting efficiency, transmittance, mode match and dark counts. For an output displacement $\delta\in\mathbb C$, the total intensities at the detector are
--
--   $$
--   I_\pm=(1-\xi)(\tau\alpha^2+|\delta|^2)+\xi|\pm\sqrt\tau\alpha+\delta|^2.
--   $$
--
--   The number laws are the normalized Poisson laws $p_\pm(n)=e^{-I_\pm}I_\pm^n/n!$. The no-click probabilities are $e^{-\nu-\eta I_\pm}$. With off decoded as minus, the average error is
--
--   $$
--   \widetilde P_D(\delta)=\frac12-e^{-\nu-\eta(\tau\alpha^2+|\delta|^2)}
--   \sinh(2\eta\xi\sqrt\tau\alpha\operatorname{Re}\delta).
--   $$
--
--   These laws are summable and the error lies in $[0,1]$. At $\tau=\xi=1$ the error equals the displacement-only receiver error. If any of $\alpha,\eta,\tau,\xi$ vanishes, it equals $1/2$ for every displacement. If all four are positive, there is a unique global minimizer over complex displacements; it is real and satisfies
--
--   $$
--   \widetilde\gamma_{\rm opt}>\xi\sqrt\tau\alpha,\qquad
--   \xi\sqrt\tau\alpha=\widetilde\gamma_{\rm opt}
--   \tanh(2\eta\xi\sqrt\tau\alpha\widetilde\gamma_{\rm opt}).
--   $$
--
--   For $\tau<1$, the local oscillator amplitude is $\delta/\sqrt{1-\tau}$; multiplying by the beam-splitter displacement coefficient gives $\delta$. At $\tau=1$, only the ideal displacement limit is used. This result keeps imperfections in the operational optimization and makes no all-power improvement claim for nonideal devices.
--
--   **Formalization Note — source correction** Printed Eq.(27) has $\tanh(2\eta\xi\alpha\widetilde\gamma_{\rm opt})$. The statement inserts the missing $\sqrt\tau$ inside the hyperbolic tangent, as required by differentiating Eq.(26). Independent moderation of this correction is pending.
-- source:
--   Discrimination of the binary coherent signal: Gaussian-operation limit and simple non-Gaussian near-optimal receivers, arXiv:0706.1038v3, PDF p. 6, Section III, Eqs. (25)–(27), beginning p.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P08

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P08

open MeasureTheory

open scoped BigOperators

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock fockKet coherentKet coherentCoefficient CoherentRealized
   displacement DisplacementRealized)

/-- PDF pp.5--6, Eqs.(25)--(27): Poisson mismatch error and unique global
optimal displacement. SOURCE CORRECTION: printed Eq.(27) omits sqrt(tau)
inside tanh; it is restored here because differentiating Eq.(26) requires it.
Printed: xi sqrt(tau) alpha = gamma tanh(2 eta xi alpha gamma).
Changed: xi sqrt(tau) alpha = gamma tanh(2 eta xi sqrt(tau) alpha gamma).
The corrected equation reduces to Eq.(23) at tau=xi=1. Independent moderation
of this correction is pending. Zero information factors give error 1/2.
Finite LO division is restricted to tau<1; the tau=1 experiment is the limit. -/
theorem imperfectTypeII_optimalDisplacement
    (alpha eta nu tau xi : ℝ) (halpha : 0 ≤ alpha)
    (heta : 0 ≤ eta) (hetaMax : eta ≤ 1) (hnu : 0 ≤ nu)
    (htau : 0 ≤ tau) (htauMax : tau ≤ 1)
    (hxi : 0 ≤ xi) (hxiMax : xi ≤ 1) :
    (∀ (delta : ℂ) (plus : Bool),
      let intensity := mismatchIntensity alpha tau xi delta plus
      0 ≤ intensity ∧
      (∀ n, 0 ≤ poissonPhotonLaw intensity n) ∧
      Summable (poissonPhotonLaw intensity) ∧
      (∑' n, poissonPhotonLaw intensity n) = 1 ∧
      Summable (fun n : ℕ => (1 - eta) ^ n * poissonPhotonLaw intensity n) ∧
      countNoClick eta nu (poissonPhotonLaw intensity) = Real.exp (-nu - eta * intensity)) ∧
    (∀ delta : ℂ,
      imperfectError alpha eta nu tau xi delta =
        1 / 2 - Real.exp (-nu - eta * (tau * alpha ^ 2 + Complex.normSq delta)) *
          Real.sinh (2 * eta * xi * Real.sqrt tau * alpha * delta.re) ∧
      0 ≤ imperfectError alpha eta nu tau xi delta ∧
        imperfectError alpha eta nu tau xi delta ≤ 1) ∧
    (∀ delta : ℂ, imperfectError alpha eta nu 1 1 delta =
      displacementError alpha eta nu delta) ∧
    (tau < 1 → ∀ delta : ℂ,
      (Real.sqrt (1 - tau) : ℂ) * localOscillator tau delta = delta) ∧
    ((alpha = 0 ∨ eta = 0 ∨ tau = 0 ∨ xi = 0) → ∀ delta : ℂ,
      imperfectError alpha eta nu tau xi delta = 1 / 2) ∧
    (0 < alpha → 0 < eta → 0 < tau → 0 < xi → ∃ gamma : ℝ,
      xi * Real.sqrt tau * alpha < gamma ∧
      xi * Real.sqrt tau * alpha =
        gamma * Real.tanh (2 * eta * xi * Real.sqrt tau * alpha * gamma) ∧
      (∀ delta : ℂ, imperfectError alpha eta nu tau xi (gamma : ℂ) ≤
        imperfectError alpha eta nu tau xi delta) ∧
      (∀ delta : ℂ, imperfectError alpha eta nu tau xi delta =
        imperfectError alpha eta nu tau xi (gamma : ℂ) → delta = (gamma : ℂ))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P08

end
