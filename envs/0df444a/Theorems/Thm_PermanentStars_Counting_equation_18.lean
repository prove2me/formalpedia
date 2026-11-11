-- Prove2me | Theorems.Thm_PermanentStars_Counting_equation_18
-- name    : PermanentStars.Counting.equation_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:55:19.743582+00:00
-- url     : https://prove2.me/theorems/c9cfb4d0-b1ca-43e7-abdb-f6a85f903f99
-- title:
--   Section 4.3, equation (18) — Output at an assigned cutoff
-- statement:
--   Fix valid cutoff data with coverage for partitions of $[n]$, and let $r\in R$. For any matrix $A$ over a commutative ring with identity, the graph $B_r$ obtained by attaching formation gadgets to the main part is an ABP and satisfies
--   $$D_{B_r}[t_r]=\sum_{\pi\in\mathcal P_n,\ r(\pi)=r}\mu(\pi)\prod_{B\in\pi}\left(\sum_{j=1}^n\prod_{i\in B}A_{ij}\right).$$
--   The product of center sums is the full left-pinned map sum, allowing distinct centers to have the same image. This is the restricted contribution assembled at one cutoff.
--
--   Differences from the source:
--   - encoding: one-based ordered leaves [n] → zero-based ordered leaves Fin n; reason: shifting leaf labels preserves every block, matrix entry, order and map weight, including n=0
--   - encoding: the constructed object is an ABP → acyclicity and the source and sink conditions are explicit conclusions; reason: the semantic graph type itself contains no correctness or acyclicity certificate
--   - encoding: sum over left-pinned maps → product of independent center sums; reason: this is equation (3) with exactly the same weights and no injectivity restriction
--   - encoding: finite star and nursery states along the source construction → finite bounded coordinate carriers, an optional open marker and isolated impossible states; reason: every source-reachable state has all counts at most n and satisfies the leaf-count invariants; no path contribution is removed
-- source:
--   Radu Curticapean, STOC 2027 submission #1331 (October 2026), Section 4.3, equation (18), PDF/printed p.10

import Definitions.Def_PermanentStars_Counting_Combined

namespace PermanentStars.Counting

/-- Section 4.3, (18), p.10; the left side is the literal graph's path sum. -/
theorem equation_18 {R : Type*} [CommRing R] (P : Cutoffs) (hP : P.Valid)
    (n : ℕ) (coverage : Covers P n) (r : ℕ) (hr : r ∈ P.R)
    (A : Matrix (Fin n) (Fin n) R) :
    (cutoffABP P r n).IsABP ∧
    (cutoffABP P r n).output (Label.eval A) = assignedSum P r A := by sorry

end PermanentStars.Counting
