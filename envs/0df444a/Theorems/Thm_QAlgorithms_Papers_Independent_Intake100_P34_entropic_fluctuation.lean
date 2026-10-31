-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_entropic_fluctuation
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.entropic_fluctuation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:01:03.462064+00:00
-- url     : https://prove2.me/theorems/ab28caa7-95f9-4537-9b6b-4177679256d5
-- title:
--   Theorem 3.1 — full entropic fluctuation theorem (seed from abstract)
-- statement:
--   Let $\mathcal O=B(\mathbb C^d)$, $d>0$, and let $L=\sum_{j=1}^M L_j$ have the specified detailed-balance decomposition with faithful invariant densities $\rho_j$. Define $L_{(\alpha)}(X)=\sum_jL_j(X\rho_j^{-\alpha_j})\rho_j^{\alpha_j}$ and $e(\alpha)=\max\{\operatorname{Re}z:z\in\operatorname{sp}L_{(\alpha)}\}$. Let $P^t_\rho$ be the law constructed from all ordered quantum-jump trajectories; set $P^0_\rho=\delta_0$.
--
--   For every real $\alpha$, the deformed semigroup is completely positive. For every initial density $\rho$ and $t\ge0$, $P^t_\rho$ is a Borel probability measure, its real exponential moments are finite, and
--
--   $$\operatorname{tr}(\rho e^{tL_{(\alpha)}}(1))=\int e^{-t\alpha\cdot s}\,dP^t_\rho(s).$$
--
--   If $e^{tL}$ is positivity improving for every $t>0$, then: all real deformations are positivity improving; the original QDS relaxes exponentially to a faithful stationary density; $e(\alpha)$ is an algebraically simple eigenvalue and every other eigenvalue has strictly smaller real part; and, for every initial state,
--
--   $$\lim_{t\to\infty}t^{-1}\log\operatorname{tr}(\rho e^{tL_{(\alpha)}}(1))=e(\alpha).$$
--
--   The function $e$ is real analytic and convex. This limit extends locally around every real parameter to its simple holomorphic eigenvalue continuation. The logarithm is an eventually defined holomorphic branch normalized by the real logarithm at the real base point. If every reservoir pair has a common time reversal, $e(1-\alpha)=e(\alpha)$. If $\rho_j=e^{-\beta_jH}/\operatorname{tr}(e^{-\beta_jH})$ for a common self-adjoint $H$ and $\beta_j>0$, then $e(\alpha+\lambda\beta^{-1})=e(\alpha)$ for every real $\lambda$.
--
--   These eight conclusions identify the entropic statistics and their long-time spectral and symmetry structure.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 7, Theorem 3.1

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

/-- PDF pp.7,20–21,26, Theorem 3.1, all eight parts. Clauses (1)–(2) require only DB;
ER scopes exactly clauses (3)–(8). Complex limits use the analytic eigenvalue and logarithm branch. -/
theorem entropic_fluctuation {d M : ℕ} (D : DBData d M) :
    (∀ a : EntropyCoordinates M, IsCPSemigroup (entropyTilt D (countingParameterEmbedding a))) ∧
    (∀ rho, IsDensityMatrix rho → ∀ t : ℝ, 0 ≤ t →
      IsProbabilityMeasure (efcs D rho t) ∧ ∀ a : EntropyCoordinates M,
        Integrable (fun s => Real.exp (-t * reservoirPairing a s)) (efcs D rho t) ∧
        traceTransform D rho t (countingParameterEmbedding a) =
          ((∫ s, Real.exp (-t * reservoirPairing a s) ∂(efcs D rho t)) : ℂ)) ∧
    (ER D →
      (∀ a : EntropyCoordinates M, ∀ t : ℝ, 0 < t → IsImproving (qdsEvolution (entropyTilt D (countingParameterEmbedding a)) t)) ∧
      RelaxesExponentially (reservoirGenerator D) (steadyDensity (reservoirGenerator D)) ∧
      (∀ a : EntropyCoordinates M, IsPerron (entropyTilt D (countingParameterEmbedding a)) (entropySpectralCGF D a)) ∧
      (∀ rho, IsDensityMatrix rho → ∀ a : EntropyCoordinates M,
        Tendsto (fun t : ℝ => finiteCGF D rho t a / t) atTop (nhds (entropySpectralCGF D a))) ∧
      AnalyticOnNhd ℝ (entropySpectralCGF D) Set.univ ∧ ConvexOn ℝ Set.univ (entropySpectralCGF D) ∧
      (∀ rho, IsDensityMatrix rho → ComplexLimit D rho) ∧
      (TR D → ∀ a : EntropyCoordinates M, entropySpectralCGF D (fun j => 1 - a j) = entropySpectralCGF D a) ∧
      (∀ H : Mat d, ∀ beta : EntropyCoordinates M, Thermal D H beta → ∀ a : EntropyCoordinates M, ∀ lam : ℝ,
        entropySpectralCGF D (fun j => a j + lam / beta j) = entropySpectralCGF D a)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
