-- Prove2me | Theorems.Thm_ReusableMatching_Supplement_claim_2
-- name    : ReusableMatching.Supplement.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:04:20.394382+00:00
-- url     : https://prove2.me/theorems/5848a25c-54e1-5798-a83b-8550995ffa62
-- title:
--   Claim 2 — forward-backward symmetry of Algorithm 2
-- statement:
--   Let $d\ge1$, let $Q_1,\dots,Q_\ell$ be any sequence of proposals, each containing one or two offline vertices, and fix an offline vertex $i$. Write $\mu^i(Q_1,\dots,Q_\ell)$ for the expected number of rounds in which Algorithm 2 matches $i$. Then
--
--   $$
--   \mu^i(Q_1,\dots,Q_\ell)=\mu^i(Q_\ell,\dots,Q_1).
--   $$
--
--   Thus reversing the proposal sequence does not change the expected number of matches of any vertex.
--
--   **Formalization Note** Rounds are zero-based and expectations are finite averages over the algorithm's fair coins.
--
--   Differences from the source:
--   - encoding: the paper numbers rounds from 1 and leaves $d\in\mathbb N$ implicit → Lean numbers list positions from 0 and binds $d\ge1$; reason: this is the same rental window and excludes the undefined $d=0$ case.
--   - encoding: the paper uses fresh fair random choices → Lean uses an equivalent finite uniform tape of three bits per round and a fixed order to label a two-element set; reason: unused bits and relabeling do not change the distribution.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Claim 2, p.18 (proof Appendix B, pp.30–33)

import Mathlib
import Definitions.Def_ReusableMatching_Supplement_OCRRun

namespace ReusableMatching.Supplement

set_option autoImplicit false

/-- **Claim 2** of Delong, Farhadi, Niazadeh, Sivan & Udwani, *Online Bipartite Matching with
Reusable Resources*, arXiv:2110.07084v2, p.18 (proof pp.30–33).

For every sequence of one- or two-vertex proposals and every offline vertex, Algorithm 2 matches
that vertex equally often in expectation when the proposal sequence is processed forward and
backward.

**Formalization Note.** Rounds and the rental window are zero-based, `d ≥ 1`, and expectations are
finite averages over the three independent fair bits per round.  The fixed order on `V` labels the
two elements of each set; Algorithm 2 is symmetric in those labels. -/
theorem claim_2 {V : Type*} [Fintype V] [LinearOrder V]
    (d : ℕ) (hd : 1 ≤ d) (Q : List (Proposal V)) (hQ : IsOCRSequence Q) (i : V) :
    mu d Q i = mu d Q.reverse i := by sorry

end ReusableMatching.Supplement
