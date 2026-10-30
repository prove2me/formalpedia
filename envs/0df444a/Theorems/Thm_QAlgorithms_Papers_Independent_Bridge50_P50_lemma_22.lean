-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_lemma_22
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.lemma_22
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:36:22.902076+00:00
-- url     : https://prove2.me/theorems/64cd6169-9f22-423b-9a00-29931b0b25f6
-- title:
--   Lemma 22: lemma 22
-- statement:
--   Let $(\Theta_n)_{n\ge1}$ be decreasing compact sets in a metric space with nonempty intersection $\Theta_\infty$. Let $f:\Theta_1\to\mathbb R$ be continuous and bounded. Then
--   $$
--   \lim_{n\to\infty}\inf_{x\in\Theta_n}f(x)=\inf_{x\in\Theta_\infty}f(x).
--   $$
--   All feasible sets are nonempty compact, so these are finite attained infima. No global continuous extension of $f$ is assumed.
--
--   This gives continuity of nested constrained extrema. **Formalization Note** The first set has Lean index zero.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 22, Lemma 22

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P50

noncomputable section

open scoped Topology BigOperators ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P50

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; these names do not create local declarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat logTwo testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage)

open QAlgorithms.Papers.Independent.Information100.P69 (entropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pairInformationVariance)

open QAlgorithms (vnEntropy traceDistance minEigenvalue)

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelSpace

/-- Lemma 22, PDF pp.22,30–31: f is continuous and bounded only on Theta_1.
The intersection hypothesis ensures all these finite infima are genuine minima. -/
theorem lemma_22 {X : Type*} [MetricSpace X]
    (Theta : ℕ → Set X) (hc : ∀ n, IsCompact (Theta n)) (hn : Antitone Theta)
    (hi : (⋂ n, Theta n).Nonempty) (f : Theta 0 → ℝ) (hf : Continuous f)
    (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    Tendsto (fun n => restrictedInf Theta f (Theta n)) atTop
      (𝓝 (restrictedInf Theta f (⋂ n, Theta n))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
