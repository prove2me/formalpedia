-- Prove2me | Theorems.Thm_SeqPostedPricing_MatroidSPM_rank_eq_card_of_maximal
-- name    : SeqPostedPricing.MatroidSPM.rank_eq_card_of_maximal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:41:37.423888+00:00
-- url     : https://prove2.me/theorems/fc1cddca-5aa7-4c89-9e08-9171c6cf3c31
-- title:
--   §4.1: in a matroid, $\mathrm{rank}(S)$ is the size of any maximal independent subset of $S$
-- statement:
--   Let $\mathcal J$ be a matroid, $S\subseteq[n]$, and $B\subseteq S$ an independent set ($B\in\mathcal J$) that is maximal in $S$: $B\cup\{e\}\notin\mathcal J$ for every $e\in S\setminus B$. Then
--
--   $$
--   |B|=\mathrm{rank}(S).
--   $$
--
--   With $S=[n]$: all bases have the same size.
--
--   Differences from the source:
--   - reading: S′ ⊂ S in rank(S) = max_{S′⊂S, S′∈J} |S′| and B ⊂ A in heredity → ⊆; reason: "the size of the largest feasible subset in S" includes S itself; for heredity B = A is trivial
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4.1, unnumbered, p. 6

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsMatroid
import Definitions.Def_SeqPostedPricing_MatroidSPM_rank

namespace SeqPostedPricing.MatroidSPM

/-- **In a matroid, the rank of a set equals the size of any maximal independent subset (all
bases have equal size).**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §4.1, unnumbered, p. 6 (PDF p. 8): "Sets in J are called independent, and maximal
independent sets are called bases. A simple consequence of the above properties is that all bases
are equal in size. Therefore, the rank of a set S ⊆ [n], is equal to the size of any maximal
independent subset of S."

If `J` is a matroid, `B ⊆ S` is independent, and no element of `S \ B` can be added to `B`
keeping it independent, then `|B| = rank(S)`. With `S = [n]` this says that every basis has size
`rank([n])`, so all bases are equal in size. -/
theorem rank_eq_card_of_maximal {n : ℕ} (Feas : Finset (Fin n) → Prop) (hmat : IsMatroid Feas)
    (S B : Finset (Fin n)) (hBS : B ⊆ S) (hB : Feas B)
    (hmax : ∀ e ∈ S, e ∉ B → ¬ Feas (insert e B)) :
    B.card = rank Feas S := by sorry

end SeqPostedPricing.MatroidSPM
