-- Prove2me | Theorems.Thm_ReusableMatching_Supplement_claim_3
-- name    : ReusableMatching.Supplement.claim_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:04:41.537395+00:00
-- url     : https://prove2.me/theorems/af99a426-efad-5e3d-ae76-7829cd802618
-- title:
--   Claim 3 — sender and receiver conditional expectations
-- statement:
--   Let $d\ge1$ and consider any proposal sequence whose first round contains two vertices. For every offline vertex $i$, let $\mu^i_{\mathrm{sender}}$ and $\mu^i_{\mathrm{receiver}}$ be the expected number of matches of $i$ conditioned on that first round being a sender or receiver, respectively. Then
--
--   $$
--   \mu^i_{\mathrm{receiver}}\le \mu^i\le \mu^i_{\mathrm{sender}}.
--   $$
--
--   This is the order relation used to close the correlated case in the proof that Algorithm 2 is a $1/32$-OCR.
--
--   **Formalization Note** The source calls the input a backward sequence. Lean quantifies over every sequence whose first proposal is randomized, which is exactly the property used there.
--
--   Differences from the source:
--   - reading: the source states the claim for a backward sequence whose first round is randomized → Lean states it for every proposal list whose first set has cardinality two; reason: every such list is a backward sequence under the paper's notation, and no additional structure is used.
--   - encoding: the paper numbers rounds from 1 and uses conditional expectations → Lean uses zero-based lists and exact finite averages over the nonempty sender/receiver subsets of the coin tape; reason: this changes no instance.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Claim 3, p.22 (proof Appendix C, p.34)

import Mathlib
import Definitions.Def_ReusableMatching_Supplement_OCRRun

namespace ReusableMatching.Supplement

set_option autoImplicit false

/-- **Claim 3** of Delong et al., arXiv:2110.07084v2, p.22 (proof p.34).

For every proposal sequence whose first round is randomized, conditioning that first round to be
a receiver can only lower the expected number of matches of a fixed vertex, while conditioning it
to be a sender can only raise that expectation.

**Formalization Note.** The paper applies this to a backward sequence; quantifying over every list
whose first proposal has two vertices is the same domain, because every such list may be regarded
as a backward sequence.  Conditional expectations are finite uniform averages, and the hypothesis
on the first proposal makes both conditioning events nonempty. -/
theorem claim_3 {V : Type*} [Fintype V] [LinearOrder V]
    (d : ℕ) (hd : 1 ≤ d) (Q : List (Proposal V)) (hQ : IsOCRSequence Q) (i : V)
    (hfirst : (proposalAt Q 0).card = 2) :
    muReceiver d Q i ≤ mu d Q i ∧ mu d Q i ≤ muSender d Q i := by sorry

end ReusableMatching.Supplement
