-- Prove2me | Theorems.Thm_StableCount_theorem_2
-- name    : StableCount.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:51:03.991049+00:00
-- url     : https://prove2.me/theorems/8d3ba81b-3256-445e-8cec-c9a0651ee684
-- title:
--   Theorem 2 — $F_h$ is a branching potential for every admissible sequence
-- statement:
--   For every admissible sequence $(h_r)_{r\ge 1}$, the function
--   $$
--   F_h(Q)=\frac12\sum_{v=1}^n\big(W(d^m_v)+W(d^w_v)\big)
--   $$
--   is a branching potential on the family $\mathcal Q$.
--
--   With the recurrence for $J$, this gives $J(Q)\le e^{F_h(Q)}$ by induction on the size of $Q$. It is the main technical ingredient of the paper.
--
--   **Formalization Note** Every clause of the definition is included: an empty member exists, $F_h\ge 0$, $F_h=0$ on an empty member, and every nonempty member branches.
--
--   Differences from the source:
--   - encoding: an instance has n ≥ 1 men and n women → every n : ℕ; reason: n = 0 has no people, one empty matching and only the empty member, and every clause holds trivially; for n ≥ 1 it is the same statement
--   - encoding: Q ∈ 𝒬: the rotation poset of a normalized instance with a chosen maximal chain, whose elements are rotations → Q : Member n, whose rotations are the chain steps Fin Q.R; reason: the convention of p.12; Proposition 2.3 (i) makes steps and rotations one-to-one, and F_h reads degrees, which a bare poset does not determine
--   - encoding: a sequence h₁, h₂, … → h : ℕ → ℝ, with h 0 never read; reason: Lean convention; same sequences
--   - encoding: λ(t) for t > 0 → lam on all of ℝ, with lam 0 = 0 from Real.log 0 = 0; reason: never hit: for an admissible sequence every argument is positive (p.15)
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), Theorem 2, p.5 (PDF p.6); proof p.15

import Mathlib
import Definitions.Def_StableCount_Potential

namespace StableCount

/-- Theorem 2 (arXiv:2611.06494, held PDF sha256 9445f6a8…, Theorem 2, p.5; Definition 4.1, p.13). For every admissible sequence `(h_r)_{r≥1}`, the
function `F_h` is a branching potential on `𝒬`.

**Formalization Note** `𝒬` is the type `Member n`, with size `R` and `J` read on the member. -/
theorem theorem_2 {n : ℕ} (h : ℕ → ℝ) (hh : IsAdmissible h) :
    IsBranchingPotential (fun Q : Member n => Q.R) (fun Q => Q.J) (fun Q => Q.Fh h) := by sorry

end StableCount
