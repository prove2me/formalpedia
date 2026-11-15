-- Prove2me | Theorems.Thm_TimeSpaceMA_constantLossFlatExtractor
-- name    : TimeSpaceMA.constantLossFlatExtractor
-- status  : Proved
-- author  : @bersubs
-- created : 2026-11-14T19:40:47.159514+00:00
-- url     : https://prove2.me/theorems/4c855973-a887-460b-b334-84847467601d
-- title:
--   Explicit padded constant-loss extractor for finite flat sources
-- statement:
--   Fix an error $0<\varepsilon\le 1/4$. There are fixed constants $A>0$ and $\Delta$ and one deterministic polynomial-time evaluator. For every $n\ge1$, threshold $0\le k\le n$, and seed width $t\ge A(\operatorname{size}(n)+\operatorname{size}(k)^4)$ with $\Delta\le k+t$, the evaluator maps an $n$-bit input and a uniform $t$-bit seed to $k+t-\Delta$ bits. Here $\operatorname{size}$ is binary length. Its output when the input is uniform on any set of at least $2^k$ points has statistical distance at most $\varepsilon$ from uniform.
--
--   This is the flat-source specialization of the constant-entropy-loss extractor of Corollary 5.8(2), with the seed width supplied as a parameter. Independent extra seed bits can be carried into the output to preserve the error and realize the specified width. The evaluator runs in polynomial time in the encoded query, which includes the two widths in unary.
-- source:
--   Ta-Shma, Umans and Zuckerman, Lossless Condensers, Unbalanced Expanders, and Extractors, Combinatorica 27 (2007), Corollary 5.8(2), PDF p. 22, https://www.cs.tau.ac.il/~amnon/Papers/TUZ.C07.pdf

import Definitions.Def_TimeSpaceMA_TUZExtractor

namespace TimeSpaceMA

open Turing.MultiTapeTM

/-- Corollary 5.8(2) of TUZ, with the seed padded to a supplied width and the
finite statistical-distance property restricted to flat sources. -/
theorem constantLossFlatExtractor (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1/4) :
    ∃ (A Δ : ℕ) (extract : ExtractorInput → ℕ),
      0 < A ∧ ComputableInPolyTime extract encExtractorInput encNat ∧
      ∀ n k t : ℕ, 1 ≤ n → k ≤ n → A*(n.size+k.size^4) ≤ t → Δ ≤ k+t →
        ∀ S : Finset (Fin (2^n)), 2^k ≤ S.card →
          FlatExtractorEvents (extractorEdge extract Δ n k t) S ε := by sorry

end TimeSpaceMA
