-- Prove2me | Theorems.Thm_StableCount_lemma_6_2
-- name    : StableCount.lemma_6_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:53:12.950188+00:00
-- url     : https://prove2.me/theorems/db908c69-9835-43b3-bf15-93c123437983
-- title:
--   Lemma 6.2 — the deficit bound $D^*_A\le\frac{h_2}{2}(N^m_A+N^w_A)$
-- statement:
--   For an admissible sequence and every initial swap $A$,
--   $$
--   D^*_A\le\frac{h_2}{2}\big(N^m_A+N^w_A\big),
--   $$
--   where $N^s_A$ is the number of exceptional labels $x\in X_A$ with $d^s_x\ge 2$.
--
--   The excess of the costs of $K_A$ over its reserved amounts is thus at most $h_2/2$ per exceptional label of degree at least two, per sex. The $h_1$ terms of the men's and the women's estimates cancel only when the two are combined.
--
--   **Formalization Note** Admissibility is the standing assumption of §6 of the paper ("Every admissible sequence", Lemma 6.1).
--
--   Differences from the source:
--   - encoding: an instance has n ≥ 1 men and n women → every n : ℕ; reason: n = 0 has no people, one empty matching and only the empty member, and every clause holds trivially; for n ≥ 1 it is the same statement
--   - encoding: Q ∈ 𝒬: the rotation poset of a normalized instance with a chosen maximal chain, whose elements are rotations → Q : Member n, whose rotations are the chain steps Fin Q.R; reason: the convention of p.12; Proposition 2.3 (i) makes steps and rotations one-to-one, and F_h reads degrees, which a bare poset does not determine
--   - encoding: a sequence h₁, h₂, … → h : ℕ → ℝ, with h 0 never read; reason: Lean convention; same sequences
--   - encoding: λ(t) for t > 0 → lam on all of ℝ, with lam 0 = 0 from Real.log 0 = 0; reason: never hit: for an admissible sequence every argument is positive (p.15)
--   - encoding: F(Q \ ↓ρ), F(Q \ ↑ρ) of the smaller member, whose women are labelled anew → Fon: the sum of W over the retained counts, with the labels of Q; reason: Lemma 3.7 makes the degrees of the smaller member the retained counts, and relabelling women does not change the sum (p.15)
--   - reading: Table 1's row "participant in an initial swap with an associated exceptional person", with a single parent u of x on p.18 → IsParent s x u, per sex: the participant of b_x in the description of sex s other than x; reason: the proof of Lemma 6.2 uses the parent "in the men's and women's descriptions" (p.23) and a^m_x = d^m_u, a^w_x = d^w_v (p.24); for B = (u, x) after A = (u, v) the women's parent has label v
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), Lemma 6.2, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_StableCount_Groups

namespace StableCount

/-- Lemma 6.2 (arXiv:2611.06494, held PDF sha256 9445f6a8…, Lemma 6.2, p.22). For every initial swap `A`, `D*_A ≤ (h₂/2)(Nᵐ_A + Nʷ_A)`.

**Formalization Note** Admissibility is the standing assumption of the section. -/
theorem lemma_6_2 {n : ℕ} (h : ℕ → ℝ) (hh : IsAdmissible h) (Q : Member n) (A : Fin Q.R)
    (hA : Q.IsInitialSwap A) :
    Q.DStar h A ≤ (h 2 / 2) * ((Q.NA .man A : ℝ) + (Q.NA .woman A : ℝ)) := by sorry

end StableCount
