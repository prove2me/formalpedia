-- Prove2me | Theorems.Thm_TenChallenges_challenge_09
-- name    : TenChallenges.challenge_09
-- status  : Open
-- author  : @utkuokur
-- created : 2026-11-04T20:47:25.61282+00:00
-- url     : https://prove2.me/theorems/c1306db3-e77b-47c6-93ec-11045fa87a5d
-- title:
--   Union-closed sets conjecture
-- statement:
--   **The union-closed sets conjecture** Every finite union-closed family $\mathcal F$ of finite sets with $\mathcal F\ne\emptyset$ and $\mathcal F\ne\{\emptyset\}$ has an element that lies in at least half of its members:
--
--   $$\exists x:\quad \delta_{\mathcal F}(x)\ \ge\ \frac12 .$$
--
--   The conjecture is equivalent to the statement $\mathrm{UC}(r)$ for all $r$ of the scaled Challenge 9, since the densities in a fixed finite family take finitely many values. The best known bound is slightly above $0.382$; the conjecture is open.
--
--   **Formalization Note.** The type `U` has decidable equality and may be in any universe; the density is `density F x : ℚ`, with denominator $\max(1,|\mathcal F|)$.
-- source:
--   Frankl's union-closed sets conjecture, as stated in H. Bruhn, O. Schaudt, The journey of the union-closed sets conjecture, Graphs Combin. 31 (2015), https://doi.org/10.1007/s00373-014-1515-0, Conjecture 1; equivalent to the universal form of V. Bajpai, N. Bowler, J. Carmesin, U. Okur, 10 Scalable Challenges in Combinatorics, AI4Math @ CICM 2026, challenge 9

import Definitions.Def_TenChallenges_Challenge_09

namespace TenChallenges
theorem challenge_09 {U : Type*} [DecidableEq U] (F : Finset (Finset U))
    (hF : IsUnionClosed F) (hne : Nondegenerate F) : ∃ x, density F x ≥ (1 / 2 : ℚ) := by sorry
end TenChallenges
