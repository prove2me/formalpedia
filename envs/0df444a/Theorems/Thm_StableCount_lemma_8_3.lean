-- Prove2me | Theorems.Thm_StableCount_lemma_8_3
-- name    : StableCount.lemma_8_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:53:04.948651+00:00
-- url     : https://prove2.me/theorems/d4b642b3-39ae-4ba4-a760-87ff84123265
-- title:
--   Lemma 8.3 — $R_A\ge bN_A$ for a positive deficit in $\mathcal P_0$
-- statement:
--   For an admissible sequence, write $b=h_2$. If $A\in\mathcal P_0$ and $D^*_A>0$, then for either sex
--   $$
--   R_A\ge bN_A.
--   $$
--   This provides, from second and third occurrences and from the savings of ordinary groups, the amount that covers each remaining positive deficit in the proof of Proposition 5.8.
--
--   **Formalization Note** Admissibility is the standing assumption of §8 of the paper, whose proof uses (H4) and Lemma 8.2.
--
--   Differences from the source:
--   - encoding: an instance has n ≥ 1 men and n women → every n : ℕ; reason: n = 0 has no people, one empty matching and only the empty member, and every clause holds trivially; for n ≥ 1 it is the same statement
--   - encoding: Q ∈ 𝒬: the rotation poset of a normalized instance with a chosen maximal chain, whose elements are rotations → Q : Member n, whose rotations are the chain steps Fin Q.R; reason: the convention of p.12; Proposition 2.3 (i) makes steps and rotations one-to-one, and F_h reads degrees, which a bare poset does not determine
--   - encoding: a sequence h₁, h₂, … → h : ℕ → ℝ, with h 0 never read; reason: Lean convention; same sequences
--   - encoding: λ(t) for t > 0 → lam on all of ℝ, with lam 0 = 0 from Real.log 0 = 0; reason: never hit: for an admissible sequence every argument is positive (p.15)
--   - encoding: F(Q \ ↓ρ), F(Q \ ↑ρ) of the smaller member, whose women are labelled anew → Fon: the sum of W over the retained counts, with the labels of Q; reason: Lemma 3.7 makes the degrees of the smaller member the retained counts, and relabelling women does not change the sum (p.15)
--   - reading: Table 1's row "participant in an initial swap with an associated exceptional person", with a single parent u of x on p.18 → IsParent s x u, per sex: the participant of b_x in the description of sex s other than x; reason: the proof of Lemma 6.2 uses the parent "in the men's and women's descriptions" (p.23) and a^m_x = d^m_u, a^w_x = d^w_v (p.24); for B = (u, x) after A = (u, v) the women's parent has label v
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), Lemma 8.3, p.29 (PDF p.30)

import Mathlib
import Definitions.Def_StableCount_Groups

namespace StableCount

/-- Lemma 8.3 (arXiv:2611.06494, held PDF sha256 9445f6a8…, Lemma 8.3, p.29). If `A ∈ 𝒫₀` and `D*_A > 0`, then for either sex `R_A ≥ b N_A`, with
`b = h₂`.

**Formalization Note** Admissibility is the standing assumption of the section. -/
theorem lemma_8_3 {n : ℕ} (h : ℕ → ℝ) (hh : IsAdmissible h) (Q : Member n) (A : Fin Q.R)
    (hA : A ∈ Q.P0) (hD : 0 < Q.DStar h A) (s : Sex) :
    h 2 * (Q.NA s A : ℝ) ≤ Q.RA h s A := by sorry

end StableCount
