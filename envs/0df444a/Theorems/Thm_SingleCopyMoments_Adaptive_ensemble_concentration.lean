-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_ensemble_concentration
-- name    : SingleCopyMoments.Adaptive.ensemble_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:49:36.053606+00:00
-- url     : https://prove2.me/theorems/32e4ec16-66e7-4c4b-a7fd-41406b391896
-- title:
--   Lemma 32 — Concentration of the hard ensembles
-- statement:
--   Let $r\ge2$ be fixed and $0<\alpha\le1/100$. Under the normalized cutoff-weighted Gaussian prior, uniformly in $\theta\in[0,\pi/r]$,
--
--   $$B_\theta=1-O(e^{-cd})$$
--
--   for an absolute $c>0$. For every fixed integer $k\ge2$ and fixed interpolation parameter,
--
--   $$p_k(\rho_\theta)\ \longrightarrow\ \alpha^k p_k(\lambda(\theta))\quad\text{in probability as }d\to\infty.$$
--
--   The Gaussian and tilted laws are genuine probabilities in every positive dimension, $B_\theta>0$, and the prior almost surely has $R_\theta<1/2$ and $\rho_\theta\succeq I/(2d)$ with trace one. These properties establish that the hard ensembles consist of physical states; they are conclusions rather than extra assumptions. The moment limit refers to one state drawn once from this physical prior.
--
--   Differences from the source:
--   - encoding: finite-dimensional states, measurable experiments, and their expectations → complex Fin d matrices, explicit Born/product measures, and normalized measurable operations; reason: the coordinate and measure conventions preserve every positive dimension and arbitrary rank; probability and integrability assertions are conclusions, not extra premises
--   - encoding: independent standard complex Gaussians and convergence in probability → independent N(0,1/2) real and imaginary coordinates, and probabilities of every positive deviation tending to zero; reason: this is exactly the specified complex Gaussian density; finite probability normalization is also asserted
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Lemma 32, (7.8), with (7.5)–(7.7), printed p. 33 (PDF p. 35); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf; PDF SHA-256 f19fd65f41a444a79243fa55aab5dfca3db6adb571b06acff78ee49932174fa9.

import Definitions.Def_SingleCopyMoments_Adaptive_Records

open MeasureTheory Filter
open scoped ENNReal Topology Matrix.Norms.L2Operator

namespace SingleCopyMoments.Adaptive

/-- Lemma 32, printed pp.33–34 (PDF pp.35–36), with the physical domain and
normalization made explicit rather than assumed. The exponential constant is absolute. -/
theorem ensemble_concentration :
    (∃ c > 0, ∀ r : ℕ, 2 ≤ r → ∀ α : ℝ, 0 < α → α ≤ 1/100 →
      ∃ C > 0, ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → 0 < d →
        ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi/r),
          |normalizer d r α θ - 1| ≤ C * Real.exp (-c*d)) ∧
    (∀ (d r : ℕ), 0 < d → 2 ≤ r → ∀ α : ℝ, 0 < α → α ≤ 1/100 →
      ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi/r),
        IsProbabilityMeasure (gaussian d r) ∧
        Integrable (fun g : Latent d r => cutoff (radial α θ g)) (gaussian d r) ∧
        0 < normalizer d r α θ ∧ IsProbabilityMeasure (prior d r α θ) ∧
        (∀ᵐ g ∂prior d r α θ, radial α θ g < 1/2 ∧
          ProjectiveMeasurementEquilibration.IsDensityMatrix (hardMatrix α θ g) ∧
          Loewner ((1/(2*(d : ℝ))) • (1 : Op d)) (hardMatrix α θ g))) ∧
    (∀ r : ℕ, 2 ≤ r → ∀ α : ℝ, 0 < α → α ≤ 1/100 →
      ∀ k : ℕ, 2 ≤ k → ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi/r), ∀ ε : ℝ, 0 < ε →
        Tendsto (fun d => ((prior d r α θ)
          {g | ε < |moment (hardMatrix α θ g) k - α^k * spectralMoment r k θ|}).toReal)
          atTop (nhds 0)) := by sorry

end SingleCopyMoments.Adaptive
