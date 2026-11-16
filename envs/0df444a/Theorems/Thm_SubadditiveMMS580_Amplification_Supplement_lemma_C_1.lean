-- Prove2me | Theorems.Thm_SubadditiveMMS580_Amplification_Supplement_lemma_C_1
-- name    : SubadditiveMMS580.Amplification.Supplement.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:00:55.758008+00:00
-- url     : https://prove2.me/theorems/edb82643-7b68-4aaa-86c3-38faf985ac3c
-- title:
--   Lemma C.1 — $\mathbb P(Z>\max_j b_jZ_j)\ge 1/(1+L)$ for independent unit exponentials when $L=\sum_j b_j\le2$
-- statement:
--   Let $Z,Z_1,\dots,Z_k$ be independent mean-one exponential random variables. If $b_j\ge0$ and $L=\sum_j b_j\le2$, then
--   $$\mathbb P\Big(Z>\max_j b_jZ_j\Big)\ge\frac{1}{1+L},$$
--   with an empty maximum equal to zero.
--
--   It is the probabilistic comparison behind the bounds of Lemma 5.5.
--
--   Differences from the source:
--   - encoding: independent mean-one exponential Z, Z_1, …, Z_k → the coordinates of the product measure of expMeasure 1 over Option (Fin k); reason: same joint law
--   - encoding: the probability bound in [0,1] → ENNReal.ofReal (1/(1+L)) ≤ the measure of the event; reason: measures take values in ℝ≥0∞; same inequality
-- source:
--   Bo Li, Ankang Sun, Toward Constant-Factor Maximin Share Guarantees for Subadditive Valuations, STOC 2027 submission #580 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/580.pdf, sha256 7de124b5706e9e49301a281a1eb418a8ae32d04bf4cf0941b969cc3cde85e485, Lemma C.1, p. 42 (PDF p. 42)

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Supplement_Reservation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation

open MultiAllocToAlloc.Subadditive MeasureTheory

namespace SubadditiveMMS580.Amplification.Supplement

/-- Lemma C.1 (Li–Sun, STOC 2027 submission #580, p. 42): let `Z, Z_1, …, Z_k` be independent
mean-one exponential random variables. If `b_j ≥ 0` and `L = ∑_j b_j ≤ 2`, then
`P(Z > max_j b_j Z_j) ≥ 1/(1 + L)` (empty maximum zero). -/
theorem lemma_C_1 (k : ℕ) (b : Fin k → ℝ) (hb : ∀ j, 0 ≤ b j) (hL : ∑ j, b j ≤ 2) :
    ENNReal.ofReal (1 / (1 + ∑ j, b j)) ≤ expPi (Fin k) {ω | maxProd b ω < ω none} := by sorry

end SubadditiveMMS580.Amplification.Supplement
