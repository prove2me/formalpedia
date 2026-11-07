-- Prove2me | Theorems.Thm_RevisitXor_lemma_6_mean
-- name    : RevisitXor.lemma_6_mean
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:30.874838+00:00
-- url     : https://prove2.me/theorems/ade50833-cb73-43df-a03c-846df9754529
-- title:
--   Lemma 6 (mean): $\mathbb E[W]\le3$
-- statement:
--   Let $M=2^m$ and $h:[2]^{2m}\to[2]$. For a uniformly random perfect matching of the complete graph on $[2]^m$, sampled as the edge sequence $X_1,\dots,X_{M/2}$, the weight $W=w(X_1,\dots,X_{M/2})$ satisfies
--
--   $$\mathbb E[W]\le3.$$
--
--   By (2) this says that the correlation of $h$ with a random $f_\pi$ is at most $3/M$ on average; it is the centering term in the concentration argument.
--
--   **Formalization Note** The expectation is the average of $W$ over all valid edge sequences.
--
--   Differences from the source:
--   - encoding: E over the random matching sampled as X₁, …, X_{M/2} → the average of W over validSeqs m; reason: the paper's sampling (p.6) with the uniform law; it holds for every m (the proof's "for M ≥ c" is not part of the statement)
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), Lemma 6, p.7

import Mathlib
import Definitions.Def_RevisitXor_validSeqs

namespace RevisitXor

/-- **Lemma 6, mean.** Viola, *Revisiting the XOR lemma*, STOC 2027 submission (manuscript of August 25, 2026, sha256
3b49e10d…716), Lemma 6, p.7: "We have E[W] ≤ 3."

**Formalization Note.** `E` is the average over the uniform law on valid edge sequences
`X₁, …, X_{M/2}` (`M = 2^m`), for every fixed `h : [2]^m × [2]^m → [2]`. The proof's "for M ≥ c" is
not a hypothesis: the bound holds for every `m` (for `m = 0` the only sequence is empty and `W = 0`;
for `M = 2`, `W ≤ 2`). -/
theorem lemma_6_mean (m : ℕ) (h : Cube m × Cube m → ZMod 2) :
    avg (validSeqs m) (W h) ≤ 3 := by sorry

end RevisitXor
