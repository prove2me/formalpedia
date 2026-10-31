-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P05_conditionalEntropy
-- name    : QAlgorithms.Papers.Independent.Intake100.P05.conditionalEntropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:47:30.97481+00:00
-- url     : https://prove2.me/theorems/4d2b2116-59ea-474f-89aa-f3fb63f0142a
-- title:
--   Three-mode AFG posterior entropy and symplectic spectrum
-- statement:
--   Let $V\ge1$, $0<T\le1$, $\chi_C\ge(1-T)/T$, $0<T_B\le1$ and $N\ge1$ be finite. Mix Bob's actual received mode with one half of a trusted EPR pair of local quadrature variance $N$ on the beamsplitter of transmittivity $T_B$, then homodyne the measured port. Let $b$ be its outcome after gain $1/\sqrt{T_B}$, and keep $F,G$ in Bob's laboratory. Put $\chi_D=(1-T_B)N/T_B$, $x=V$, $y=T(V+\chi_C)$, $z=\sqrt{T(V^2-1)}$, $\Delta=x^2+y^2-2z^2$ and $D=xy-z^2$. Define
--
--   $$
--   A=\frac{y+xD+\chi_D\Delta}{y+\chi_D},\qquad
--   B=\frac{D(x+\chi_DD)}{y+\chi_D}.
--   $$
--
--   The outcome has normal density of variance $y+\chi_D$, positive for every real $b$. The actual normalized three-mode posterior $\rho_{AFG\mid b}$ has covariance independent of $b$. Its symplectic eigenvalues are $\lambda_3,\lambda_4,1$, with $\lambda_3\ge\lambda_4\ge1$, where
--
--   $$
--   \lambda_{3,4}^2=\frac{A\pm\sqrt{A^2-4B}}2,\qquad
--   (\lambda_j^2)^2-A\lambda_j^2+B=0\ (j=3,4),\qquad
--   S(\rho_{AFG\mid b})=G\!\left(\frac{\lambda_3-1}2\right)+G\!\left(\frac{\lambda_4-1}2\right).
--   $$
--
--   Here $G$ is thermal entropy in bits with $G(0)=0$. Entropy is finite and independent of the outcome, even though conditional means vary with $b$. The third vacuum symplectic eigenvalue is retained in the actual six-dimensional characteristic polynomial. The construction and independent full-Hermite-basis entropy make this an identity about the measured optical state, not a covariance-defined surrogate.
-- source:
--   Continuous-variable quantum key distribution protocols over noisy channels, arXiv:0806.3954v2, PDF p. 4, Eqs.(7)–(8), continued from p.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P05

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P05

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:0806.3954v2, PDF pp.3–4, Eqs.(7)–(8): the constructed
three-mode AFG posterior has outcome-independent covariance and entropy.
All three symplectic eigenvalues are retained: lambda_3, lambda_4, and 1.
Bob's rescaled outcome has variance y+chiD, and Eve never receives F,G.
The target evaluates entropy; it makes no operational key-capacity claim. -/
theorem conditionalEntropy (V T chiC TB N : ℝ) (hV : 1 ≤ V)
    (hT : 0 < T) (hTupper : T ≤ 1) (hC : (1 - T) / T ≤ chiC)
    (hTB : 0 < TB) (hTBupper : TB ≤ 1) (hN : 1 ≤ N) :
    let chiD := detectorNoise TB N
    let A := conditionalA V T chiC chiD
    let B := conditionalB V T chiC chiD
    let l3 := conditionalLambda V T chiC chiD true
    let l4 := conditionalLambda V T chiC chiD false
    1 ≤ l4 ∧ l4 ≤ l3 ∧ 0 ≤ A ^ 2 - 4 * B ∧
    (l3 ^ 2) ^ 2 - A * l3 ^ 2 + B = 0 ∧
    (l4 ^ 2) ^ 2 - A * l4 ^ 2 + B = 0 ∧
    ∀ b : ℝ,
      0 < afgBornDensity V T chiC TB N b ∧
      afgBornDensity V T chiC TB N b = normalPDF (T * (V + chiC) + chiD) b ∧
      IsContinuousDensityKernel volume (afgPosterior V T chiC TB N b) ∧
      QAlgorithms.Papers.Independent.Dependency50.P33.IsDensity
        (afgNumberCoefficients (afgPosterior V T chiC TB N b)) ∧
      (∀ m n : (ℕ × ℕ) × ℕ, Integrable
        (fun xy : AFGPosition × AFGPosition =>
          star (afgNumberWave m xy.1) * afgPosterior V T chiC TB N b xy.1 xy.2 *
            afgNumberWave n xy.2) volume) ∧
      ContDiff ℝ 2 (afgCharacteristic (afgPosterior V T chiC TB N b)) ∧
      afgCovariance (afgPosterior V T chiC TB N b) =
        afgCovariance (afgPosterior V T chiC TB N 0) ∧
      (afgOmega * afgCovariance (afgPosterior V T chiC TB N b)).charpoly =
        (Polynomial.X ^ 2 + 1) *
          (Polynomial.X ^ 2 + Polynomial.C (l3 ^ 2)) *
          (Polynomial.X ^ 2 + Polynomial.C (l4 ^ 2)) ∧
      afgEntropyBits (afgPosterior V T chiC TB N b) < ⊤ ∧
      afgEntropyBits (afgPosterior V T chiC TB N b) = ENNReal.ofReal
        (thermalEntropyBits ((l3 - 1) / 2) + thermalEntropyBits ((l4 - 1) / 2)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P05

end
