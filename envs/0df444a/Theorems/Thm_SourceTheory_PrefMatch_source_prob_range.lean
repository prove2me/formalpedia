-- Prove2me | Theorems.Thm_SourceTheory_PrefMatch_source_prob_range
-- name    : SourceTheory.PrefMatch.source_prob_range
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:10.557668+00:00
-- url     : https://prove2.me/theorems/63ae20be-4484-4fb1-8a2f-57308c72fe71
-- title:
--   Proof of Obs. 1, p. 8779, with (5), p. 8771 — the a-neutral probability of a uniform source takes every value in [0, 1]
-- statement:
--   Assume structural Assumption 1 for $(\succcurlyeq, U, W)$ on the events $\mathcal E$. Let $\mathcal A$ be a source (a subalgebra of $\mathcal E$ on which $W$ is convex ranged) that is uniform with a-neutral probability measure $P_{\mathcal A}$, and let $w_{\mathcal A}$ be its source function, so that $W = w_{\mathcal A} \circ P_{\mathcal A}$ on $\mathcal A$. Then $P_{\mathcal A}$ takes every value in $[0,1]$:
--
--   $$\forall q \in [0,1]\ \ \exists A \in \mathcal A : \ P_{\mathcal A}(A) = q.$$
--
--   The paper proves this for risk in the proof of Observation 1 ("Convex rangedness implies that $w$'s domain is the entire $[0,1]$") and states that the case of a uniform source is identical. It is what lets every probability $p \in [0,1]$ be realized by an event of the source, so that conditions on events translate into conditions on $w_{\mathcal A}$ for all $p$.
--
--   **Formalization Note.** The probability measure is only finitely additive; the paper defers the general (finitely additive) proof to its Online Appendix A.
-- source:
--   Baillon et al. (2025), Management Science 71(10), App. B, proof of Observation 1, p. 8779, applied to a uniform source per (5), p. 8771

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

namespace SourceTheory.PrefMatch

open Set SourceTheory.Uniform

/-- Proof of Observation 1 (p. 8779), applied to a uniform source by (5) (p. 8771): convex
rangedness forces the a-neutral probability `P_𝒜` of a uniform source to take every value in
`[0, 1]`. -/
theorem source_prob_range {S Γ : Type*} (𝓔 : Set (Set S)) (pref : (S → Γ) → (S → Γ) → Prop)
    (U : Γ → ℝ) (W : Set S → ℝ) (h1 : Assumption1 𝓔 pref U W)
    (𝒜 : Set (Set S)) (h𝒜 : IsSource 𝓔 W 𝒜) (PA : Set S → ℝ) (wA : ℝ → ℝ)
    (hPA : IsUniformWith pref U 𝒜 PA) (hwA : IsSourceFunction W 𝒜 PA wA) :
    ∀ q ∈ Icc (0 : ℝ) 1, ∃ A ∈ 𝒜, PA A = q := by sorry

end SourceTheory.PrefMatch
