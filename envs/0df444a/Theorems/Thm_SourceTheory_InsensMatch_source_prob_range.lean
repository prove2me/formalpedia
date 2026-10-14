-- Prove2me | Theorems.Thm_SourceTheory_InsensMatch_source_prob_range
-- name    : SourceTheory.InsensMatch.source_prob_range
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:04.040809+00:00
-- url     : https://prove2.me/theorems/935f4ebd-814b-4bba-b57b-a75cd8ff6b7d
-- title:
--   Proof of Observation 1, p. 8779 (with (5), p. 8771) — the a-neutral probability of a uniform source takes every value in [0, 1]
-- statement:
--   Assume structural Assumption 1. Let $\mathcal A$ be a source (a subalgebra of events on which $W$ is convex ranged) that is uniform with a-neutral probability $P_{\mathcal A}$ and source function $w_{\mathcal A}$, so that $W = w_{\mathcal A} \circ P_{\mathcal A}$ on $\mathcal A$. Then $P_{\mathcal A}$ takes every value in the unit interval:
--
--   $$\forall q \in [0,1]\ \exists A \in \mathcal A:\ P_{\mathcal A}(A) = q.$$
--
--   The paper proves this range property for risk in the proof of Observation 1 ("Convex rangedness implies that w's domain is the entire [0,1]") and states that the proof for a source function (5) is identical. It is what lets every triple of probabilities $p_1, p_2, p_3$ summing to 1 be realised by a partition of the source, which turns preference conditions on events into conditions on functions of probabilities.
--
--   **Formalization Note.** $P_{\mathcal A}$ is only finitely additive; the paper calls the countably additive case elementary and defers the general case to its Online Appendix A.
-- source:
--   Baillon et al. (2025), Management Science 71(10), proof of Observation 1, p. 8779; (5), p. 8771

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.InsensMatch

open Set

/-- Proof of Observation 1 (p. 8779), applied to a uniform source by (5) (p. 8771): convex
rangedness forces the a-neutral probability `P_𝒜` of a uniform source to take every value in
`[0, 1]`. -/
theorem source_prob_range {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : SourceTheory.Uniform.Assumption1 𝓔 pref U W)
    (𝒜 : Set (Set S)) (h𝒜 : SourceTheory.Uniform.IsSource 𝓔 W 𝒜) (PA : Set S → ℝ) (wA : ℝ → ℝ)
    (hPA : SourceTheory.Uniform.IsUniformWith pref U 𝒜 PA) (hwA : SourceTheory.Uniform.IsSourceFunction W 𝒜 PA wA) :
    ∀ q ∈ Icc (0 : ℝ) 1, ∃ A ∈ 𝒜, PA A = q := by sorry

end SourceTheory.InsensMatch
