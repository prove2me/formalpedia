-- Prove2me | Theorems.Thm_PermanentStars_Counting_fact_4_2
-- name    : PermanentStars.Counting.fact_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:33.400199+00:00
-- url     : https://prove2.me/theorems/3efe33c8-cdd6-49a9-ada6-e0f77349803e
-- title:
--   Fact 4.2 — Deleting small blocks preserves assignment
-- statement:
--   Fix valid positive cutoffs $R$ and rational fractions $\alpha_r$ as in Definition 4.1, and assume every partition of $[n]$ has an admissible cutoff. Let $\pi$ partition any subset of $[n]$, fix $r\in R$, and set $\rho=\{B\in\pi:|B|>r\}$. Then
--   $$r(\pi)=r\quad\Longleftrightarrow\quad r(\rho)=r.$$
--   Both assignments use the ambient $n$. This identifies the assignment test needed when the deferred large blocks are formed.
--
--   Differences from the source:
--   - encoding: largest admissible cutoff on the covered domain → Option-valued assignment, with none on uncovered inputs; reason: the standing coverage hypothesis ensures that no relevant partition uses the default case
--   - encoding: partitions of subsets of [n] → Mathlib Finpartition of subsets of Fin n; reason: shifting labels preserves all blocks, cardinalities and the ambient n
-- source:
--   Radu Curticapean, STOC 2027 submission #1331 (October 2026), Fact 4.2, PDF/printed p.9

import Definitions.Def_PermanentStars_Counting_Partitions

namespace PermanentStars.Counting

/-- Fact 4.2, p.9, including the standing coverage assumption of Definition 4.1. -/
theorem fact_4_2 (P : Cutoffs) (hP : P.Valid) (n : ℕ) (coverage : Covers P n)
    (S : Finset (Fin n)) (pi : Finpartition S) (r : ℕ) (hr : r ∈ P.R) :
    assigned P n pi.parts = some r ↔
      assigned P n (pi.parts.filter (fun B => r < B.card)) = some r := by sorry

end PermanentStars.Counting
