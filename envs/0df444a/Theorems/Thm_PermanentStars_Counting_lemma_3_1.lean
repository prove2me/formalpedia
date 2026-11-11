-- Prove2me | Theorems.Thm_PermanentStars_Counting_lemma_3_1
-- name    : PermanentStars.Counting.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:16.034003+00:00
-- url     : https://prove2.me/theorems/1835f68f-4b1c-4aa8-b20a-031a6f8987c8
-- title:
--   Lemma 3.1 — Basic ABP correctness
-- statement:
--   Let $A$ be an $n\times n$ matrix over any commutative ring with identity, including the zero ring. Let $B_{\mathrm{basic}}$ be the graph of Begin, Grow and Close transitions in §3. Then it is an ABP and
--   $$D_{B_{\mathrm{basic}}}[t]=\operatorname{per}(A).$$
--   The assertion concerns the concrete transition graph, including the empty input, and provides the basic correctness statement used by the later cutoff construction.
--
--   Differences from the source:
--   - encoding: one-based leaves [n] and row products → zero-based Fin n and Mathlib column products; reason: shifting leaf labels and inverting the summed permutation preserves every matrix instance, including n=0
--   - encoding: the constructed object is an ABP → acyclicity and the source and sink conditions are explicit conclusions; reason: the semantic graph type itself contains no correctness or acyclicity certificate
--   - encoding: finite star and nursery states along the source construction → finite bounded coordinate carriers, an optional open marker and isolated impossible states; reason: every source-reachable state has all counts at most n and satisfies the leaf-count invariants; no path contribution is removed
-- source:
--   Radu Curticapean, STOC 2027 submission #1331 (October 2026), Lemma 3.1, PDF/printed p.6

import Definitions.Def_PermanentStars_Counting_Basic

namespace PermanentStars.Counting

/-- Lemma 3.1, p.6; the graph is the concrete (7)--(9), not a correctness certificate. -/
theorem lemma_3_1 {R : Type*} [CommRing R] (n : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    (basicABP n).IsABP ∧ (basicABP n).output (Label.eval A) = Matrix.permanent A := by sorry

end PermanentStars.Counting
