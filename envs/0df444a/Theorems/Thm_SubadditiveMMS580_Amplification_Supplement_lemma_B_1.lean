-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_Supplement_lemma_B_1
-- name    : SubadditiveMMS580.Amplification.Supplement.lemma_B_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T19:55:42.276289+00:00
-- url     : https://prove2.me/theorems/8301d0d2-e255-462f-82c5-17c6e68c0202
-- title:
--   Lemma B.1 — for the first admissible dyadic $d$, $F_d(x)\ge 1/(11x-5)$
-- statement:
--   For $x\ge1$ and a dyadic integer $d\ge2$ (a power of two), let
--   $$F_d(x)=\frac{(1-x/d)^+}{2d-1},\qquad x_d=\frac{4d^2}{6d-1}.$$
--   If $d$ is the **first** dyadic integer at least two with $x\le x_d$ (so $x>x_{d'}$ for every dyadic $2\le d'<d$), then
--   $$F_d(x)\ge\frac{1}{11x-5}.$$
--
--   This turns the family of grouping guarantees into the smooth bound $1/(11x-5)$ of Proposition 4.3.
--
--   Differences from the source:
--   - encoding: d dyadic, d ≥ 2, the first one with x ≤ x_d → d = 2^k with k ≥ 1, x ≤ x_{2^k}, and x_{2^{k'}} < x for every 1 ≤ k' < k; reason: the dyadic integers at least two are exactly 2^k with k ≥ 1, and 'first' means every smaller one fails x ≤ x_{d'}
-- source:
--   Bo Li, Ankang Sun, Toward Constant-Factor Maximin Share Guarantees for Subadditive Valuations, STOC 2027 submission #580 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/580.pdf, sha256 7de124b5706e9e49301a281a1eb418a8ae32d04bf4cf0941b969cc3cde85e485, Lemma B.1, p. 42 (PDF p. 42)

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Partitioning
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_LittleCharity_MMS_Setting

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Supplement

/-- Lemma B.1 (Li–Sun, STOC 2027 submission #580, p. 42): for `x ≥ 1` and dyadic `d ≥ 2`, with
`F_d(x) = (1 − x/d)^+/(2d − 1)` and `x_d = 4d²/(6d − 1)`: if `d = 2^k` (`k ≥ 1`) is the first
dyadic integer at least two with `x ≤ x_d`, then `F_d(x) ≥ 1/(11x − 5)`. -/
theorem lemma_B_1 (x : ℝ) (hx : 1 ≤ x) (k : ℕ) (hk : 1 ≤ k)
    (hle : x ≤ xd ((2 : ℝ) ^ k))
    (hfirst : ∀ k' : ℕ, 1 ≤ k' → k' < k → xd ((2 : ℝ) ^ k') < x) :
    1 / (11 * x - 5) ≤ Fd ((2 : ℝ) ^ k) x := by sorry

end SubadditiveMMS580.Amplification.Supplement
