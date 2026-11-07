-- Prove2me | Theorems.Thm_StableCount_proposition_5_8
-- name    : StableCount.proposition_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:57.002324+00:00
-- url     : https://prove2.me/theorems/67f7bb29-7c4b-45b3-854d-4c12bfc98697
-- title:
--   Proposition 5.8 — the deficits of the initial swaps are covered by the unreserved amounts
-- statement:
--   For every admissible sequence and every $Q\in\mathcal Q$,
--   $$
--   \sum_{A\in\mathcal P}D^*_A\le\frac{U_m+U_w}{2}+\frac12\sum_{\rho\in\mathcal O}\big(\Delta^m_\rho+\Delta^w_\rho\big),
--   $$
--   where $\mathcal P$ is the set of initial swaps, $\mathcal O$ the set of ordinary rotations, $U_s$ the unreserved occurrence surplus of sex $s$, and $\Delta^s_\rho$ the unused amount of the first group of $\rho$.
--
--   The partition of the labels into initial-swap blocks and ordinary first groups reduces (BC) to this estimate.
--
--   Differences from the source:
--   - encoding: an instance has n ≥ 1 men and n women → every n : ℕ; reason: n = 0 has no people, one empty matching and only the empty member, and every clause holds trivially; for n ≥ 1 it is the same statement
--   - encoding: Q ∈ 𝒬: the rotation poset of a normalized instance with a chosen maximal chain, whose elements are rotations → Q : Member n, whose rotations are the chain steps Fin Q.R; reason: the convention of p.12; Proposition 2.3 (i) makes steps and rotations one-to-one, and F_h reads degrees, which a bare poset does not determine
--   - encoding: a sequence h₁, h₂, … → h : ℕ → ℝ, with h 0 never read; reason: Lean convention; same sequences
--   - encoding: λ(t) for t > 0 → lam on all of ℝ, with lam 0 = 0 from Real.log 0 = 0; reason: never hit: for an admissible sequence every argument is positive (p.15)
--   - encoding: F(Q \ ↓ρ), F(Q \ ↑ρ) of the smaller member, whose women are labelled anew → Fon: the sum of W over the retained counts, with the labels of Q; reason: Lemma 3.7 makes the degrees of the smaller member the retained counts, and relabelling women does not change the sum (p.15)
--   - reading: Table 1's row "participant in an initial swap with an associated exceptional person", with a single parent u of x on p.18 → IsParent s x u, per sex: the participant of b_x in the description of sex s other than x; reason: the proof of Lemma 6.2 uses the parent "in the men's and women's descriptions" (p.23) and a^m_x = d^m_u, a^w_x = d^w_v (p.24); for B = (u, x) after A = (u, v) the women's parent has label v
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), Proposition 5.8, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_StableCount_Groups

namespace StableCount

/-- Proposition 5.8 (arXiv:2611.06494, held PDF sha256 9445f6a8…, Proposition 5.8, p.21). For every admissible sequence and every `Q ∈ 𝒬`,
`∑_{A∈𝒫} D*_A ≤ (U_m + U_w)/2 + ½ ∑_{ρ∈𝒪} (∆ᵐ_ρ + ∆ʷ_ρ)`. -/
theorem proposition_5_8 {n : ℕ} (h : ℕ → ℝ) (hh : IsAdmissible h) (Q : Member n) :
    ∑ A ∈ Q.initialSwaps, Q.DStar h A ≤
      (Q.U h .man + Q.U h .woman) / 2 +
        (1 / 2) * ∑ i ∈ Q.ordinary, (Q.Delta h .man i + Q.Delta h .woman i) := by sorry

end StableCount
