-- Prove2me | Theorems.Thm_SingleCopyMoments_Adaptive_good_record_tv
-- name    : SingleCopyMoments.Adaptive.good_record_tv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:49:43.01978+00:00
-- url     : https://prove2.me/theorems/af3f2ca9-c559-454e-8f1d-5cdee879209f
-- title:
--   Lemma 34 — Total variation from good records
-- statement:
--   Under the hypotheses of Lemma 33, let $\nu$ be the same full seeded protocol run on $I/d$ and $p_\theta=Z_\theta/B_\theta$. These are the actual densities of the original ensemble transcript laws. Their endpoint total variation satisfies
--
--   $$\operatorname{TV}(P_0^{(T)},P_{\pi/r}^{(T)})\le\frac12\int_0^{\pi/r}\int_{G_\kappa}|\partial_\theta p_\theta(H)|\,d\nu(H)\,d\theta+d\left(\frac{2eT}{\kappa d}\right)^\kappa.$$
--
--   The endpoint density difference and the derivative integrals are integrable. The event $G_\kappa$ is fixed across interpolation parameters. This compares the endpoints directly under the original unstopped laws; only the bound on their variation is divided into good and exceptional records.
--
--   Differences from the source:
--   - encoding: finite-dimensional states, measurable experiments, and their expectations → complex Fin d matrices, explicit Born/product measures, and normalized measurable operations; reason: the coordinate and measure conventions preserve every positive dimension and arbitrary rank; probability and integrability assertions are conclusions, not extra premises
--   - encoding: total variation and the path integral of the genuine densities → the half-L1 density difference, a density-to-ensemble-law equality, and integrability conclusions; reason: the equality prevents an unrelated likelihood or a default-zero integral from replacing the original experiment
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), Lemma 34, (7.21), printed p. 37 (PDF p. 39); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf; PDF SHA-256 f19fd65f41a444a79243fa55aab5dfca3db6adb571b06acff78ee49932174fa9.

import Definitions.Def_SingleCopyMoments_Adaptive_Records

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

namespace SingleCopyMoments.Adaptive

/-- Lemma 34, printed p.37 (PDF p.39). Densities below are certified as the
original ensemble laws, so the L1 expression is their actual TV distance. -/
theorem good_record_tv (r : ℕ) (hr : 2 ≤ r) (α κ : ℝ)
    (hα : 0 < α) (hα₁ : α ≤ 1/100) (hκ : 1 ≤ κ) (hακ : α ≤ 1/(8*κ))
    (d T : ℕ) (hd : 0 < d) (hT : T ≤ d) (hTκ : 2*(T : ℝ) < κ*d)
    (P : Protocol d) (R : Refinement hd P) :
    (∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi/r),
      ensembleLaw hd P r α θ T = (referenceLaw hd P T).withDensity
        (fun H => ENNReal.ofReal (densityAt R r α θ T H))) ∧
    (∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi/r),
      IntegrableOn (fun H => |deriv (fun u => densityAt R r α u T H) θ|)
        (goodRecords R T κ) (referenceLaw hd P T)) ∧
    Integrable (fun H => |densityAt R r α 0 T H - densityAt R r α (Real.pi/r) T H|)
      (referenceLaw hd P T) ∧
    IntegrableOn (fun θ => derivativeIntegral R r α θ T κ) (Set.Icc 0 (Real.pi/r)) ∧
    endpointTV R r α T ≤ (1/2 : ℝ) *
      (∫ θ in Set.Icc 0 (Real.pi/r), derivativeIntegral R r α θ T κ) +
      (d : ℝ) * (2*Real.exp 1*T/(κ*d))^κ := by sorry

end SingleCopyMoments.Adaptive
