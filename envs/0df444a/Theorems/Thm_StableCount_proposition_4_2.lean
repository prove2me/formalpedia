-- Prove2me | Theorems.Thm_StableCount_proposition_4_2
-- name    : StableCount.proposition_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:51:30.656298+00:00
-- url     : https://prove2.me/theorems/970a634c-acfd-474d-a045-be870e2ebafc
-- title:
--   Proposition 4.2 — the branching criterion (BC)
-- statement:
--   For every admissible sequence and every nonempty $Q\in\mathcal Q$,
--   $$
--   \sum_{v\in V}\lambda\big(p^*(b_v)\big)\le\sum_{v\in V}q^*(b_v).
--   $$
--   Labels sharing the same first rotation are counted separately.
--
--   The criterion produces a rotation $\rho=b_v$ with $\lambda(p^*(\rho))\le q^*(\rho)$, equivalently $e^{-p^*(\rho)}+e^{-q^*(\rho)}\le 1$, which is the inequality needed to branch on $\rho$.
--
--   Differences from the source:
--   - encoding: an instance has n ≥ 1 men and n women → every n : ℕ; reason: n = 0 has no people, one empty matching and only the empty member, and every clause holds trivially; for n ≥ 1 it is the same statement
--   - encoding: Q ∈ 𝒬: the rotation poset of a normalized instance with a chosen maximal chain, whose elements are rotations → Q : Member n, whose rotations are the chain steps Fin Q.R; reason: the convention of p.12; Proposition 2.3 (i) makes steps and rotations one-to-one, and F_h reads degrees, which a bare poset does not determine
--   - encoding: a sequence h₁, h₂, … → h : ℕ → ℝ, with h 0 never read; reason: Lean convention; same sequences
--   - encoding: λ(t) for t > 0 → lam on all of ℝ, with lam 0 = 0 from Real.log 0 = 0; reason: never hit: for an admissible sequence every argument is positive (p.15)
--   - encoding: F(Q \ ↓ρ), F(Q \ ↑ρ) of the smaller member, whose women are labelled anew → Fon: the sum of W over the retained counts, with the labels of Q; reason: Lemma 3.7 makes the degrees of the smaller member the retained counts, and relabelling women does not change the sum (p.15)
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), Proposition 4.2, p.15 (PDF p.16), (BC)

import Mathlib
import Definitions.Def_StableCount_Potential

namespace StableCount

/-- Proposition 4.2 (arXiv:2611.06494, held PDF sha256 9445f6a8…, Proposition 4.2, p.15, display (BC)). For every admissible sequence and every
nonempty `Q ∈ 𝒬`, `∑_{v∈V} λ(p*(b_v)) ≤ ∑_{v∈V} q*(b_v)`. Labels sharing the same first rotation are counted
separately. -/
theorem proposition_4_2 {n : ℕ} (h : ℕ → ℝ) (hh : IsAdmissible h) (Q : Member n) (hQ : Q.R ≠ 0) :
    ∑ v ∈ Q.V, Q.atFirst (fun i => lam (Q.pStar h i)) v ≤ ∑ v ∈ Q.V, Q.atFirst (Q.qStar h) v := by sorry

end StableCount
