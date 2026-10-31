-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P34_trajectory_unraveling
-- name    : QAlgorithms.Papers.Independent.Intake100.P34.trajectory_unraveling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:25:16.570734+00:00
-- url     : https://prove2.me/theorems/a3db1c78-d986-4821-abda-3124969f726d
-- title:
--   §6, (39)–(40) — path-space construction of entropic statistics
-- statement:
--   Assume the specified detailed-balance decomposition, with no ER or TR, and fix an initial density $\rho$ and $t>0$. Set $K=\sum_j(\Phi_j(1)/2+iT_j)$ and $\mathcal K(X)=-K^*X-XK$. Use the constructed frequency components $\Phi_{j,\omega}$, $\rho_t=e^{t\mathcal K^*}(\rho)$ and $\Phi_{j,\omega,s}=e^{-s\mathcal K}\Phi_{j,\omega}e^{s\mathcal K}$. The measure $\mu^t_\rho$ sums every jump count and every finite label sequence with ordered-simplex Lebesgue density $\operatorname{tr}(\rho_t\Phi_{j_N,\omega_N,s_N}\cdots\Phi_{j_1,\omega_1,s_1}(1))$, including the empty-path mass. It is a probability measure. The rate map $s_j(\xi)=t^{-1}\sum_{k:j_k=j}\omega_k$ is measurable and $P^t_\rho$ is its pushforward. Moreover,
--
--   $$L_{(\alpha)}=\mathcal K+\sum_{j,\omega}e^{-\alpha_j\omega}\Phi_{j,\omega},\qquad\operatorname{tr}(\rho e^{tL_{(\alpha)}}(1))=\int e^{-t\alpha\cdot s(\xi)}\,d\mu^t_\rho(\xi).$$
--
--   All these real exponential moments are integrable. This constructs and identifies EFCS from trajectories rather than postulating a law with the required transform.
-- source:
--   Entropic fluctuations of quantum dynamical semigroups, arXiv:1305.4409v2, PDF p. 21, §6, (39)–(40)

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

/-- PDF pp.20–21, (39)–(40): explicit all-count ordered-simplex path measure, normalization,
measurable rate pushforward and Laplace identity. DB suffices; t is strictly positive. -/
theorem trajectory_unraveling {d M : ℕ} (D : DBData d M) (rho : Mat d)
    (hrho : IsDensityMatrix rho) (t : ℝ) (ht : 0 < t) :
    IsProbabilityMeasure (trajectoryMeasure D rho t) ∧ Measurable (pathRate D t) ∧
    efcs D rho t = Measure.map (pathRate D t) (trajectoryMeasure D rho t) ∧
    (∀ a : EntropyCoordinates M,
      entropyTilt D (countingParameterEmbedding a) = noJump D +
        ∑ j, ∑ w ∈ frequencies (D.rho j),
          (Real.exp (-a j * w) : ℂ) • frequencyComponent (D.rho j) (D.Phi j) w) ∧
    (∀ a : EntropyCoordinates M,
      Integrable (fun xi => Real.exp (-t * reservoirPairing a (pathRate D t xi))) (trajectoryMeasure D rho t) ∧
      traceTransform D rho t (countingParameterEmbedding a) =
        ((∫ xi, Real.exp (-t * reservoirPairing a (pathRate D t xi)) ∂(trajectoryMeasure D rho t)) : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P34

end
