-- Prove2me | Theorems.Thm_ReusableMatching_Supplement_proposition_1
-- name    : ReusableMatching.Supplement.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:05:17.748823+00:00
-- url     : https://prove2.me/theorems/9e4e83dc-ea6d-4406-b8d6-77362435a820
-- title:
--   Proposition 1 — Algorithm 2 is a $1/32$-OCR
-- statement:
--   For every rental duration $d\ge1$ and every sequence of one- or two-vertex proposals, Algorithm 2 is a $1/32$-OCR in the sense of Definition 1. Concretely, for every offline vertex $i$ and every round $j$, its exact matching probability $\Delta\mu_j^i$ satisfies the appropriate one of the four bounds in (8): zero off the proposal, $p_j^i$ in a singleton, $p_j^i/2$ after no recent occurrence, and
--
--   $$
--   \frac{p_j^i}{2}+\frac1{32}\bigl(p_{j'}^i-\Delta\mu_{j'}^i\bigr)
--   $$
--
--   when $j'=\operatorname{prev}_j^i$ lies within the last $d-1$ rounds.
--
--   This supplies the positive correlation parameter used by OPD's factor-revealing program.
--
--   Differences from the source:
--   - encoding: the source uses $\operatorname{prev}_j^i=-\infty$ when no earlier proposal exists → Lean uses `none` and places it in the same uncorrelated case; reason: this is the option-type representation of the identical case split.
--   - encoding: the paper uses one-based rounds and fresh fair choices → Lean uses zero-based lists, binds $d\ge1$, and takes exact finite averages over a uniform three-bit tape; reason: these conventions preserve every proposal sequence and probability.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Proposition 1, p.16; Definition 1, eq. (8), p.16; proof pp.18–22

import Mathlib
import Definitions.Def_ReusableMatching_Supplement_OCRRun

namespace ReusableMatching.Supplement

set_option autoImplicit false

/-- **Proposition 1** of Delong et al., arXiv:2110.07084v2, p.16 (analysis pp.18–22): Algorithm 2
is a `1/32`-OCR algorithm in the sense of Definition 1.

This is the full four-case inequality (8), for every finite offline vertex set, every rental
duration `d ≥ 1`, every sequence of nonempty proposals of cardinality at most two, every round,
and every vertex.

**Formalization Note.** `none` represents the paper's `prev = -∞`; it belongs to the uncorrelated
case.  All probabilities are exact finite averages over Algorithm 2's fresh fair coins. -/
theorem proposition_1 {V : Type*} [Fintype V] [LinearOrder V]
    (d : ℕ) (hd : 1 ≤ d) (Q : List (Proposal V)) (hQ : IsOCRSequence Q) :
    IsGammaOCR d Q (1 / 32 : ℝ) := by sorry

end ReusableMatching.Supplement
