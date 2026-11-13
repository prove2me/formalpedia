-- Prove2me | Theorems.Thm_StableCount_lemma_3_7
-- name    : StableCount.lemma_3_7
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:50:11.382037+00:00
-- url     : https://prove2.me/theorems/3072c56e-0d8b-41cd-8bc3-e2c6d0dc71ab
-- title:
--   Lemma 3.7 — the recurrence $J(Q)=J(Q\setminus\downarrow\rho)+J(Q\setminus\uparrow\rho)$
-- statement:
--   For every rotation $\rho\in Q$,
--   $$
--   J(Q)=J(Q\setminus\downarrow\rho)+J(Q\setminus\uparrow\rho).
--   $$
--   Both smaller posets are rotation posets of normalized instances on the same people, with degrees equal to their numbers of retained occurrences.
--
--   This is the branching step for the induction on the size of $Q$.
--
--   Differences from the source:
--   - encoding: an instance has n ≥ 1 men and n women → every n : ℕ; reason: n = 0 has no people, one empty matching and only the empty member, and every clause holds trivially; for n ≥ 1 it is the same statement
--   - encoding: Q ∈ 𝒬: the rotation poset of a normalized instance with a chosen maximal chain, whose elements are rotations → Q : Member n, whose rotations are the chain steps Fin Q.R; reason: the convention of p.12; Proposition 2.3 (i) makes steps and rotations one-to-one, and F_h reads degrees, which a bare poset does not determine
--   - encoding: "both smaller posets are rotation posets … on the same people" → ∃ Q₁ Q₂ : Member n with IsRestriction, J equal to the count on the retained set, and deg Qᵢ s p the retained count of the actual person p; reason: people rather than labels, since a woman's label is defined anew (p.14)
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), Lemma 3.7, p.12 (PDF p.13), eq. (5)

import Mathlib
import Definitions.Def_StableCount_Member

namespace StableCount

/-- Lemma 3.7 (arXiv:2611.06494, held PDF sha256 9445f6a8…, Lemma 3.7, p.12, display (5)). For every rotation `ρ ∈ Q`,
`J(Q) = J(Q \ ↓ρ) + J(Q \ ↑ρ)`. Both smaller posets are rotation posets of normalized instances on the
same people, with degrees equal to their numbers of retained occurrences. -/
theorem lemma_3_7 {n : ℕ} (Q : Member n) (i : Fin Q.R) :
    Q.J = Q.Jon (Finset.univ \ Q.down i) + Q.Jon (Finset.univ \ Q.up i) ∧
    ∃ (Q₁ Q₂ : Member n) (e₁ : {j // j ∈ Finset.univ \ Q.down i} ≃ Fin Q₁.R)
      (e₂ : {j // j ∈ Finset.univ \ Q.up i} ≃ Fin Q₂.R),
      Q.IsRestriction (Finset.univ \ Q.down i) Q₁ e₁ ∧
      Q.IsRestriction (Finset.univ \ Q.up i) Q₂ e₂ ∧
      Q₁.J = Q.Jon (Finset.univ \ Q.down i) ∧ Q₂.J = Q.Jon (Finset.univ \ Q.up i) ∧
      (∀ s p, Q₁.deg s p = Q.degOn (Finset.univ \ Q.down i) s p) ∧
      ∀ s p, Q₂.deg s p = Q.degOn (Finset.univ \ Q.up i) s p := by sorry

end StableCount
