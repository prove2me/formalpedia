-- Prove2me | Theorems.Thm_PermanentStars_Counting_corollary_4_5
-- name    : PermanentStars.Counting.corollary_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:55:04.476215+00:00
-- url     : https://prove2.me/theorems/781c3387-cb0e-46a7-b02f-b8d170f5b58b
-- title:
--   Corollary 4.5 — Combined ABP correctness
-- statement:
--   Fix valid cutoff data and suppose every partition of $[n]$ has an admissible cutoff. Form $B$ from disjoint copies of the concrete cutoff ABPs by adding a fresh source and sink and unit transitions to their endpoints. For any $n\times n$ matrix over any commutative ring with identity, $B$ is an ABP and
--   $$D_B[t]=\operatorname{per}(A).$$
--   The statement concerns the constructed disjoint union and includes $n=0$. It assembles the per-cutoff correctness statements.
--
--   Differences from the source:
--   - encoding: one-based leaves [n] and row products → zero-based Fin n and Mathlib column products; reason: shifting leaf labels and inverting the summed permutation preserves every matrix instance, including n=0
--   - encoding: the constructed object is an ABP → acyclicity and the source and sink conditions are explicit conclusions; reason: the semantic graph type itself contains no correctness or acyclicity certificate
--   - encoding: finite star and nursery states along the source construction → finite bounded coordinate carriers, an optional open marker and isolated impossible states; reason: every source-reachable state has all counts at most n and satisfies the leaf-count invariants; no path contribution is removed
-- source:
--   Radu Curticapean, STOC 2027 submission #1331 (October 2026), Corollary 4.5, PDF/printed p.10

import Definitions.Def_PermanentStars_Counting_Combined

namespace PermanentStars.Counting

/-- Corollary 4.5, p.10. The combined graph has disjoint cutoff copies and unit joins. -/
theorem corollary_4_5 {R : Type*} [CommRing R] (P : Cutoffs) (hP : P.Valid)
    (n : ℕ) (coverage : Covers P n) (A : Matrix (Fin n) (Fin n) R) :
    (combinedABP P n).IsABP ∧ (combinedABP P n).output (Label.eval A) = Matrix.permanent A := by sorry

end PermanentStars.Counting
