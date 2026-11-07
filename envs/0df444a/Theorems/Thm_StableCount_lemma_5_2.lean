-- Prove2me | Theorems.Thm_StableCount_lemma_5_2
-- name    : StableCount.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:18.520298+00:00
-- url     : https://prove2.me/theorems/e2c775fa-cbaa-40d9-aa84-94834956ca21
-- title:
--   Lemma 5.2 — the sum of the upper losses is $\sum_v H_{d_v}+\Omega$
-- statement:
--   For either sex,
--   $$
--   \sum_{v\in V}q(b_v)=\sum_{v\in V}H_{d_v}+\Omega.
--   $$
--   The first occurrence of person $v$ contributes $(s(b_v)-2)h_1$ to $\Omega$.
--
--   This identity rewrites the right-hand side of (BC) as a sum of contributions of each person's rotations, which is what the later accounting allocates.
--
--   **Formalization Note** The second sentence includes that $b_v$ is the occurrence of rank one of the person of either sex with label $v$.
--
--   Differences from the source:
--   - encoding: an instance has n ≥ 1 men and n women → every n : ℕ; reason: n = 0 has no people, one empty matching and only the empty member, and every clause holds trivially; for n ≥ 1 it is the same statement
--   - encoding: Q ∈ 𝒬: the rotation poset of a normalized instance with a chosen maximal chain, whose elements are rotations → Q : Member n, whose rotations are the chain steps Fin Q.R; reason: the convention of p.12; Proposition 2.3 (i) makes steps and rotations one-to-one, and F_h reads degrees, which a bare poset does not determine
--   - encoding: a sequence h₁, h₂, … → h : ℕ → ℝ, with h 0 never read; reason: Lean convention; same sequences
--   - encoding: F(Q \ ↓ρ), F(Q \ ↑ρ) of the smaller member, whose women are labelled anew → Fon: the sum of W over the retained counts, with the labels of Q; reason: Lemma 3.7 makes the degrees of the smaller member the retained counts, and relabelling women does not change the sum (p.15)
--   - generalization: the standing sequence h₁ ≥ h₂ ≥ ⋯ > 0 of §4.1 → every h : ℕ → ℝ; reason: the identity is a rearrangement of a finite sum and uses no property of h; it specializes to the source by taking its h
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), Lemma 5.2, p.17 (PDF p.18), eq. (11)

import Mathlib
import Definitions.Def_StableCount_Groups

namespace StableCount

/-- Lemma 5.2 (arXiv:2611.06494, held PDF sha256 9445f6a8…, Lemma 5.2, p.17, display (11)). For either sex, `∑_{v∈V} q(b_v) = ∑_{v∈V} H_{d_v} + Ω`.
The first occurrence of person `v` contributes `(s(b_v) − 2) h₁` to `Ω`.

**Formalization Note** The identity holds for every sequence `h`, without the page's standing `h₁ ≥ h₂ ≥ ⋯ > 0`.
The second sentence includes that `b_v` is the rank-one occurrence of the person of either sex with label `v`. -/
theorem lemma_5_2 {n : ℕ} (h : ℕ → ℝ) (Q : Member n) (s : Sex) :
    ∑ v ∈ Q.V, Q.atFirst (Q.qLoss h s) v = ∑ v ∈ Q.V, Hsum h (Q.dL s v) + Q.Omega h s ∧
    ∀ (v : Fin n) (hv : v ∈ Q.V),
      Q.first v hv ∈ Q.chainOf s (Q.person s v) ∧
      Q.rank s (Q.person s v) (Q.first v hv) = 1 ∧
      Q.omegaTerm h s v (Q.first v hv) = ((Q.s (Q.first v hv) : ℝ) - 2) * h 1 := by sorry

end StableCount
