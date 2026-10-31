-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P05_unconditionalEntropy
-- name    : QAlgorithms.Papers.Independent.Intake100.P05.unconditionalEntropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:46:39.162855+00:00
-- url     : https://prove2.me/theorems/69199484-eff2-465f-bca2-d1d73eba1813
-- title:
--   AB entropy and complete two-mode symplectic spectrum
-- statement:
--   Let $V\ge1$, $0<T\le1$ and $\chi_C\ge(1-T)/T$ be finite, and let $\rho_{AB}$ be the actual EPR-plus-attenuator output constructed above. Set $x=V$, $y=T(V+\chi_C)$, $z=\sqrt{T(V^2-1)}$, $\Delta=x^2+y^2-2z^2$ and $D=xy-z^2$. Its ordered symplectic eigenvalues $\lambda_1\ge\lambda_2\ge1$ satisfy
--
--   $$
--   \lambda_{1,2}^2=\frac{\Delta\pm\sqrt{\Delta^2-4D^2}}2,\qquad
--   S(\rho_{AB})=G\!\left(\frac{\lambda_1-1}2\right)+G\!\left(\frac{\lambda_2-1}2\right),
--   \quad G(t)=(t+1)\log_2(t+1)-t\log_2t.
--   $$
--
--   The entropy is finite, with $0\log_2 0=0$. The complete characteristic polynomial of the actual covariance's symplectic matrix is $(s^2+\lambda_1^2)(s^2+\lambda_2^2)$. Entropy is independently defined from the full density's matrix elements in the normalized Hermite basis and its von Neumann finite-compression entropy, rather than by this formula. This gives the unconditioned term in the reverse-reconciliation calculation.
-- source:
--   Continuous-variable quantum key distribution protocols over noisy channels, arXiv:0806.3954v2, PDF p. 3, Eqs.(5)–(6)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P05

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P05

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:0806.3954v2, PDF p.3, Eqs.(5)–(6): actual finite AB entropy
and both symplectic eigenvalues, ordered lambda_1>=lambda_2>=1. Number
coefficients come from the constructed output kernel. The characteristic
polynomial identifies the symplectic spectrum with its multiplicities;
no entropy identity or proposed spectrum is assumed in a binder. -/
theorem unconditionalEntropy (V T chiC : ℝ) (hV : 1 ≤ V)
    (hT : 0 < T) (hTupper : T ≤ 1) (hC : (1 - T) / T ≤ chiC) :
    QAlgorithms.Papers.Independent.Dependency50.P33.IsDensity
      (numberCoefficients (channelKernel V T chiC)) ∧
    (∀ m n : ℕ × ℕ, Integrable
      (fun xy : (ℝ × ℝ) × (ℝ × ℝ) =>
        star (twoModeNumberWave m xy.1) * channelKernel V T chiC xy.1 xy.2 *
          twoModeNumberWave n xy.2) volume) ∧
    1 ≤ abLambda V T chiC false ∧
    abLambda V T chiC false ≤ abLambda V T chiC true ∧
    0 ≤ (abDelta V T chiC) ^ 2 - 4 * (abD V T chiC) ^ 2 ∧
    (∀ upper : Bool, (abLambda V T chiC upper) ^ 2 =
      (abDelta V T chiC + (if upper then 1 else -1) *
        Real.sqrt ((abDelta V T chiC) ^ 2 - 4 * (abD V T chiC) ^ 2)) / 2) ∧
    (sourceOmega * kernelCovariance (channelKernel V T chiC)).charpoly =
      (Polynomial.X ^ 2 + Polynomial.C ((abLambda V T chiC true) ^ 2)) *
      (Polynomial.X ^ 2 + Polynomial.C ((abLambda V T chiC false) ^ 2)) ∧
    kernelEntropyBits (channelKernel V T chiC) < ⊤ ∧
    kernelEntropyBits (channelKernel V T chiC) = ENNReal.ofReal
      (thermalEntropyBits ((abLambda V T chiC true - 1) / 2) +
       thermalEntropyBits ((abLambda V T chiC false - 1) / 2)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P05

end
