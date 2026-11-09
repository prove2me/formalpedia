-- Prove2me | Theorems.Thm_RandomIsetThreshold_Degree_lemma_4_4
-- name    : RandomIsetThreshold.Degree.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:17:50.83458+00:00
-- url     : https://prove2.me/theorems/5847ea79-35a5-4e32-ac03-d16de6b9be55
-- title:
--   Lemma 4.4 — first-step instability probability
-- statement:
--   Let $r\ge2$, $n\ge4$, $0<\varepsilon\le1$, $0<\kappa<1/e$, and $0<\xi\le1/2$. Suppose $e/n^{r-1}\le p\le1-n^{-\xi}$ and $\tau=\log(1/\kappa)/(pL^r)\le1/2$. Use the computed Section 4 parameters and the events of §4.1, under the genuine resampling path with a shared independent arbitrary seed. Let $f$ be any seedwise measurable real-vector output.
--
--   Assume that some $\tau_0\in[\sqrt\kappa/(pL^r),1]$ satisfies $\operatorname{NS}_{\tau_0}(f)\le\kappa L$. Then
--
--   $$\Pr(S_{0,1}^{\mathrm c})\le\frac{200^2}{\varepsilon}\sqrt\kappa\log(1/\kappa).$$
--
--   The witness $\tau_0$ is allowed to exceed the lower endpoint of its interval. This estimate connects the noise assumption to the path stability event; it requires no norm bound.
--
--   Differences from the source:
--   - encoding: vertices [n], all unordered r-sets, and real edge probabilities → Fin n, the subtype of r-element finsets, and unitInterval parameters; reason: order-preserving relabeling; interior biases are imposed or follow from the source regime
--   - encoding: independent random seeds and nonnegative expectations → an arbitrary measurable probability space, product sampling, seedwise measurability, and ENNReal moments; reason: the standing measurability convention makes probabilities meaningful; infinite moments retain their value
--   - encoding: the Section 4 correlated hypergraphs and E, S, M, O, C events → the genuine Bernoulli resampling path, computed parameters (32), and the events on pages 13–14; reason: path masks and replacement bits are independent, with the same external seed at every time
--   - generalization: the asymptotically fixed admissible Section 4 function → any measurable function satisfying the same noise condition in the explicit nonasymptotic regime; reason: the proof (43) and Markov bound use only this regime and the displayed noise hypothesis
-- source:
--   Matthew Cho, Lutz Warnke, STOC 2027 submission #260 (October 2026), p. 16, Lemma 4.4, equation (42)

import Mathlib
import Definitions.Def_RandomIsetThreshold_Degree_ResamplingPath

open MeasureTheory
open scoped ENNReal BigOperators
universe u_lemma_4_4

namespace RandomIsetThreshold.Degree

theorem lemma_4_4
(n r : ℕ) (hr : 2 ≤ r) (hn : 4 ≤ n) (p : unitInterval)
    (ε κ : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (hκ : 0 < κ ∧ κ < 1 / Real.exp 1)
    (ξ : ℝ) (hξ : 0 < ξ ∧ ξ ≤ 1 / 2)
    (hreg : Regime n r p (Real.exp 1) ξ)
    (hτ : noiseRate n r p κ ≤ 1 / 2)
    {Ω : Type u_lemma_4_4} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Cube n r → Ω → Vector n) (hf : SeedMeasurable f)

    (hnoise : ∃ τ₀ : unitInterval,
      Real.sqrt κ / ((p : ℝ) * scale n r p ^ r) ≤ (τ₀ : ℝ) ∧
        noiseSensitivity p τ₀ μ f ≤ ENNReal.ofReal (κ * scale n r p)) :
    sectionProbability (n := n) (r := r) p κ μ (eventS01 p ε f)ᶜ ≤
      200 ^ 2 / ε * Real.sqrt κ * Real.log (1 / κ) := by sorry

end RandomIsetThreshold.Degree
