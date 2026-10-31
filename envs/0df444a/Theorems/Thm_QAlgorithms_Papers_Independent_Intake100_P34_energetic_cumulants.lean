-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_energetic_cumulants
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.energetic_cumulants
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:19:05.447201+00:00
-- url     : https://prove2.me/theorems/5ff744cd-3d69-4dfa-a1b4-d195a3e3c667
-- title:
--   §3.5, (19)–(21) — energetic cumulants and symmetries
-- statement:
--   Assume detailed balance, positivity improvement, and common-Hamiltonian Gibbs densities with $\beta_j>0$. Define $Q^t_\rho$ as the pushforward of $P^t_\rho$ under $s_j\mapsto-s_j/\beta_j$. For every initial state, nonnegative time and real $\alpha$, its positive-exponential moment is finite and
--
--   $$\int e^{t\alpha\cdot\phi}\,dQ^t_\rho(\phi)=\operatorname{tr}(\rho e^{tL_{(\alpha/\beta)}}(1)).$$
--
--   The positive-Laplace cumulant is therefore $\chi(\alpha)=e(\alpha/\beta)$, and
--
--   $$\lim_{t\to\infty}t^{-1}\log\int e^{t\alpha\cdot\phi}dQ^t_\rho=\chi(\alpha),\quad\partial_j\chi(0)=\phi_j,\quad\partial_k\partial_j\chi(0)=\frac{\partial_k\partial_j e(0)}{\beta_j\beta_k}.$$
--
--   For every real $\lambda$, $\chi(\alpha+\lambda1)=\chi(\alpha)$. Common time reversal further gives $\chi(\alpha)=\chi(\beta-\alpha)$. The definition and ES sign correct the printed mismatch between positive- and negative-Laplace conventions. These formulas express energy transport through entropy transport.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 11, §3.5, (19)–(21)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P34

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P34

open QAlgorithms (IsDensityMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P26 (Mat commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P69 (Faithful)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate finiteRelativeEntropyNats entropyObservable)

open QAlgorithms.Papers.Independent.Claimed50.P43 (chaotic)

/-- PDF p.3: complex linear superoperators. -/
local notation "GeneratorMap" => fun d : ℕ => MatrixMap (Fin d) (Fin d)

/-- PDF p.11, (19)–(21). SOURCE CORRECTION: the positive-Laplace transform forces
chi(a)=e(a/beta), hence ES chi(a)=chi(beta-a). The printed opposite signs use a different,
negative-Laplace convention and conflict with the displayed positive-exponential identity. -/
theorem energetic_cumulants {d M : ℕ} (D : DBData d M) (hER : ER D)
    (H : Mat d) (beta : EntropyCoordinates M) (hThermal : Thermal D H beta) :
    (∀ rho, IsDensityMatrix rho → ∀ t : ℝ, 0 ≤ t → IsProbabilityMeasure (energyLaw D beta rho t) ∧
      ∀ a : EntropyCoordinates M, Integrable (fun x => Real.exp (t * reservoirPairing a x)) (energyLaw D beta rho t) ∧
        traceTransform D rho t (countingParameterEmbedding (fun j => a j / beta j)) =
          ((∫ x, Real.exp (t * reservoirPairing a x) ∂(energyLaw D beta rho t)) : ℂ)) ∧
    (∀ rho, IsDensityMatrix rho → ∀ a : EntropyCoordinates M,
      Tendsto (fun t : ℝ => Real.log (∫ x, Real.exp (t * reservoirPairing a x) ∂(energyLaw D beta rho t)) / t)
        atTop (nhds (energyCGF D beta a))) ∧
    (∀ j, countingCoordinateDerivative (energyCGF D beta) j 0 = energyMean D H j) ∧
    (∀ j k, coordinateHessianAtZero (energyCGF D beta) j k = coordinateHessianAtZero (entropySpectralCGF D) j k / (beta j * beta k)) ∧
    (∀ a : EntropyCoordinates M, ∀ lam : ℝ, energyCGF D beta (fun j => a j + lam) = energyCGF D beta a) ∧
    (TR D → ∀ a : EntropyCoordinates M, energyCGF D beta a = energyCGF D beta (fun j => beta j - a j)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
