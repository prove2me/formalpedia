-- Prove2me | Theorems.Thm_RandomIsetThreshold_Degree_lemma_4_5
-- name    : RandomIsetThreshold.Degree.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:17:26.039227+00:00
-- url     : https://prove2.me/theorems/36da3c28-d1c4-462b-8071-e98f4eaa12b3
-- title:
--   Lemma 4.5 — all three exceptional-event estimates
-- statement:
--   For $r\ge2$ and $0<\varepsilon\le1$, choose $d_0\ge e$, $0<\xi_0\le1/2$ and an integer $n_1\ge4$, depending only on $r,\varepsilon$. For all $d\ge d_0$, $0<\xi\le\xi_0$, $n\ge n_1$, $d/n^{r-1}\le p\le1-n^{-\xi}$, and $0<\kappa<1/e$ with $\tau\le1/2$, let the Section 4 parameters and events be computed as stated above. For any measurable random output $f$, set $\ell=\log(n^{r-1}p)$. Then all three estimates hold:
--
--   $$\Pr(M^{\mathrm c})\le T^2e^{-\ell L},\qquad\Pr(O^{\mathrm c}\cap M)\le T^{4K}e^{-\ell L},$$
--   $$\Pr(C^{\mathrm c}\cap E\cap M)\le T^{2K}e^{-\ell L/(4r(r-1))}.$$
--
--   These are the exceptional-event bounds used with Lemma 4.2. No event bound or typical independent-set existence is assumed in the model.
--
--   Differences from the source:
--   - encoding: vertices [n], all unordered r-sets, and real edge probabilities → Fin n, the subtype of r-element finsets, and unitInterval parameters; reason: order-preserving relabeling; interior biases are imposed or follow from the source regime
--   - encoding: independent random seeds and nonnegative expectations → an arbitrary measurable probability space, product sampling, seedwise measurability, and ENNReal moments; reason: the standing measurability convention makes probabilities meaningful; infinite moments retain their value
--   - encoding: the Section 4 correlated hypergraphs and E, S, M, O, C events → the genuine Bernoulli resampling path, computed parameters (32), and the events on pages 13–14; reason: path masks and replacement bits are independent, with the same external seed at every time
--   - encoding: constants with specified parameter dependencies → nested existential witnesses before the parameters on which they may not depend; reason: makes the source uniformity explicit without changing an instance
--   - generalization: thresholds allowed to depend on δ, with the admissible f fixed and κ later chosen → thresholds depending only on r,ε and bounds for every measurable f and every κ with τ ≤ 1/2; reason: the three union-bound proofs on pp. 18–20 use no δ or noise hypothesis and are uniform in κ once the rate is valid
-- source:
--   Matthew Cho, Lutz Warnke, STOC 2027 submission #260 (October 2026), p. 16, Lemma 4.5, equations (44)–(46); proofs pp. 18–20

import Mathlib
import Definitions.Def_RandomIsetThreshold_Degree_ResamplingPath

open MeasureTheory
open scoped ENNReal BigOperators
universe u_lemma_4_5

namespace RandomIsetThreshold.Degree

theorem lemma_4_5
(r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) :
    ∃ d₀ : ℝ, Real.exp 1 ≤ d₀ ∧
      ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ ≤ 1 / 2 ∧ ∃ n₁ : ℕ, 4 ≤ n₁ ∧
      ∀ (d ξ : ℝ), d₀ ≤ d → 0 < ξ → ξ ≤ ξ₀ →
      ∀ n : ℕ, n₁ ≤ n → ∀ p : unitInterval, Regime n r p d ξ →
      ∀ κ : ℝ, 0 < κ ∧ κ < 1 / Real.exp 1 → noiseRate n r p κ ≤ 1 / 2 →
      ∀ (Ω : Type u_lemma_4_5) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (f : Cube n r → Ω → Vector n), SeedMeasurable f →
      let T := horizon n r p ε κ
      let K := blockCount ε
      let L := scale n r p
      let ell := Real.log ((n : ℝ) ^ (r - 1) * (p : ℝ))
      sectionProbability (n := n) (r := r) p κ μ (eventM p ε κ)ᶜ ≤ (T : ℝ) ^ 2 * Real.exp (-ell * L) ∧
      sectionProbability (n := n) (r := r) p κ μ ((eventO p ε κ)ᶜ ∩ eventM p ε κ) ≤
        (T : ℝ) ^ (4 * K) * Real.exp (-ell * L) ∧
      sectionProbability (n := n) (r := r) p κ μ ((eventC p ε κ f)ᶜ ∩ eventE p ε κ f ∩ eventM p ε κ) ≤
        (T : ℝ) ^ (2 * K) * Real.exp (-ell * L / (4 * (r : ℝ) * ((r : ℝ) - 1))) := by sorry

end RandomIsetThreshold.Degree
