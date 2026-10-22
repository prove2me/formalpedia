-- Prove2me | Theorems.Thm_SeqSocialLearning_Adequate_lemma_7
-- name    : SeqSocialLearning.Adequate.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:06.675586+00:00
-- url     : https://prove2.me/theorems/2c8cf01b-bb28-4df6-b813-136e71c9fee7
-- title:
--   Lemma 7, p. 17 — conditioning P ∈ ∆(∆(Ω)) on K gives a barycenter Q̃ ≪ P̃ with dQ̃/dP̃ ≤ 1/P(K)
-- statement:
--   For $\mathbf P \in \Delta(\Delta(\Omega))$, the barycenter $\tilde{\mathbf P} \in \Delta(\Omega)$ is
--   $$
--   \tilde{\mathbf P}(E) = \int_{\Delta(\Omega)} \lambda(E)\, d\mathbf P(\lambda).
--   $$
--   Let $K \subseteq \Delta(\Omega)$ be measurable with $\mathbf P(K) > 0$, and let $\mathbf Q = \mathbf P(\cdot\mid K)$. Then $\tilde{\mathbf Q}$ is absolutely continuous with respect to $\tilde{\mathbf P}$, and
--   $$
--   \frac{d\tilde{\mathbf Q}}{d\tilde{\mathbf P}} \le \frac{1}{\mathbf P(K)} \qquad \tilde{\mathbf P}\text{-almost surely}.
--   $$
--
--   With Lemma 5, this gives the bounded-density condition used in the proof of Theorem 1.
--
--   **Formalization Note** $\Delta(\Delta(\Omega))$ is a probability measure on the Giry space `Measure Ω` that is concentrated on probability measures. The barycenter is `Measure.join` and $\mathbf P(\cdot\mid K)$ is `ProbabilityTheory.cond`.
-- source:
--   Arieli & Mueller-Frank, A General Analysis of Sequential Social Learning, SSRN 2466903 (version of February 21, 2019), p. 17, Lemma 7 (barycenter (9))

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace SeqSocialLearning.Adequate

/-- **Lemma 7** (p. 17). Let `P ∈ ∆(∆(Ω))` and let `K ⊆ ∆(Ω)` be measurable with `P(K) > 0`,
and `Q = P(· | K)`. The barycenter `Q̃` is absolutely continuous with respect to `P̃`, and
`dQ̃/dP̃ ≤ 1/P(K)` `P̃`-almost surely. Here `P̃(E) = ∫ λ(E) dP(λ)` is `P.join`. -/
theorem lemma_7 {Ω : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    (P : Measure (Measure Ω)) [IsProbabilityMeasure P]
    (hP : ∀ᵐ lam ∂P, IsProbabilityMeasure lam)
    (K : Set (Measure Ω)) (hK : MeasurableSet K) (hPK : 0 < P K) :
    (P[|K]).join ≪ P.join ∧
      ∀ᵐ ω ∂P.join, (P[|K]).join.rnDeriv P.join ω ≤ (P K)⁻¹ := by sorry

end SeqSocialLearning.Adequate
