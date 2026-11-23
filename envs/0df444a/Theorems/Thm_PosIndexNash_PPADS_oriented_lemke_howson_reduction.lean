-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_oriented_lemke_howson_reduction
-- name    : PosIndexNash.PPADS.oriented_lemke_howson_reduction
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:44:44.912985+00:00
-- url     : https://prove2.me/theorems/40ba3dea-9976-4328-b9b3-bdf140315830
-- title:
--   Theorem 3.2, circuit step — the oriented Lemke–Howson graph gives a Sink-of-Line reduction
-- statement:
--   Positive-Index Nash on nondegenerate games with strictly positive rational payoffs reduces in polynomial time to normalized Sink-of-Line:
--   $$
--   \textsc{Positive-Index Nash with Positive Payoffs}\;\le_p\;\textsc{Sink-of-Line}.
--   $$
--   For a fixed missing label $\ell$, the instance map constructs Boolean circuits for the oriented predecessor and successor maps on the basis representation (18) of the missing-$\ell$ Lemke–Howson graph. Invalid strings are fixed points of both circuits. Lemma 3.1 makes the artificial equilibrium the distinguished source, makes every internal vertex and every non-artificial source satisfy $P(S(v))=v$, and makes precisely the non-artificial endpoints of Shapley index $+1$ sinks. Every answer is decoded by (7) into an exact rational Nash equilibrium of index $+1$.
--
--   This is the substantive circuit construction in the proof of Theorem 3.2. Its proof uses the oriented-path properties and polynomial-time local pivoting supplied by Lemma 3.1, together with exact rational Gaussian elimination and the support systems (4).
--
--   **Formalization Note** The statement packages circuit construction, normalization, and answer decoding as the platform's polynomial-time search reduction on binary encodings. The promise includes positivity and nondegeneracy, exactly the hypotheses of Lemma 3.1.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), pp. 18–19, proof of Theorem 3.2, using p. 16, Lemma 3.1, p. 15, eq. (7), and p. 13, eq. (4)

import Mathlib
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_PosIndexNash_PPADS_SinkOfLine
import Definitions.Def_PosIndexNash_PPADS_PositivePayoffNash

open PosIndexNash.PPADS

theorem PosIndexNash.PPADS.oriented_lemke_howson_reduction :
    CardinalMatching.SearchReduces PositivePayoffNash SinkOfLine := by sorry
