-- Prove2me | Theorems.Thm_RandomIsetThreshold_Degree_lemma_4_2
-- name    : RandomIsetThreshold.Degree.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:17:28.578419+00:00
-- url     : https://prove2.me/theorems/4714e7da-089b-479f-b424-74a40c0a39c7
-- title:
--   Lemma 4.2 — upper bound on simultaneous success and stability
-- statement:
--   Let $r\ge2$, $n\ge4$, $0<\varepsilon\le1$, $0<\kappa<1/e$, and $0<\xi\le1/2$. Suppose $e/n^{r-1}\le p\le1-n^{-\xi}$ and $\tau=\log(1/\kappa)/(pL^r)\le1/2$. Use the computed Section 4 parameters and the events of §4.1, under the genuine resampling path with a shared independent arbitrary seed. Let $f$ be any seedwise measurable real-vector output.
--
--   Then
--
--   $$\Pr(E\cap S)\le\Pr(M^{\mathrm c})+\Pr(O^{\mathrm c}\cap M)+\Pr(C^{\mathrm c}\cap E\cap M).$$
--
--   This is the event comparison needed for the impossibility branch. All five events retain their hypergraph and selector meanings.
--
--   Differences from the source:
--   - encoding: vertices [n], all unordered r-sets, and real edge probabilities → Fin n, the subtype of r-element finsets, and unitInterval parameters; reason: order-preserving relabeling; interior biases are imposed or follow from the source regime
--   - encoding: independent random seeds and nonnegative expectations → an arbitrary measurable probability space, product sampling, seedwise measurability, and ENNReal moments; reason: the standing measurability convention makes probabilities meaningful; infinite moments retain their value
--   - encoding: the Section 4 correlated hypergraphs and E, S, M, O, C events → the genuine Bernoulli resampling path, computed parameters (32), and the events on pages 13–14; reason: path masks and replacement bits are independent, with the same external seed at every time
--   - generalization: the function and parameters fixed after the asymptotic choices in Section 4 → all functions under the explicit nonasymptotic bounds n ≥ 4, d ≥ e, ξ ≤ 1/2 and τ ≤ 1/2; reason: the event argument uses only these bounds, not noise admissibility or the later sufficiently-large thresholds; the original regime specializes to them
-- source:
--   Matthew Cho, Lutz Warnke, STOC 2027 submission #260 (October 2026), p. 14, Lemma 4.2, equation (34)

import Mathlib
import Definitions.Def_RandomIsetThreshold_Degree_ResamplingPath

open MeasureTheory
open scoped ENNReal BigOperators
universe u_lemma_4_2

namespace RandomIsetThreshold.Degree

theorem lemma_4_2
(n r : ℕ) (hr : 2 ≤ r) (hn : 4 ≤ n) (p : unitInterval)
    (ε κ : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (hκ : 0 < κ ∧ κ < 1 / Real.exp 1)
    (ξ : ℝ) (hξ : 0 < ξ ∧ ξ ≤ 1 / 2)
    (hreg : Regime n r p (Real.exp 1) ξ)
    (hτ : noiseRate n r p κ ≤ 1 / 2)
    {Ω : Type u_lemma_4_2} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Cube n r → Ω → Vector n) (hf : SeedMeasurable f)
 :
    sectionProbability (n := n) (r := r) p κ μ (eventE p ε κ f ∩ eventS p ε κ f) ≤
      sectionProbability (n := n) (r := r) p κ μ (eventM p ε κ)ᶜ +
      sectionProbability (n := n) (r := r) p κ μ ((eventO p ε κ)ᶜ ∩ eventM p ε κ) +
      sectionProbability (n := n) (r := r) p κ μ ((eventC p ε κ f)ᶜ ∩ eventE p ε κ f ∩ eventM p ε κ) := by sorry

end RandomIsetThreshold.Degree
