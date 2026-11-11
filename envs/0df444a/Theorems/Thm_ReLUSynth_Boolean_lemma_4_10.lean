-- Prove2me | Theorems.Thm_ReLUSynth_Boolean_lemma_4_10
-- name    : ReLUSynth.Boolean.lemma_4_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:11:44.503921+00:00
-- url     : https://prove2.me/theorems/7477b893-5edd-45b0-b4b1-206490e84a40
-- title:
--   Lemma 4.10 — three-copy binary reference: positive integer weights reproducing the threshold ∑ 2^i y ≥ 2^r − 1 are exactly 2^i
-- statement:
--   Let $Q=2^r-1$ with $r\ge2$. Assign positive integer weights $\omega_{i,\gamma}$ to $k_i\ge3$ copies $\gamma$ of every level $i\in\{0,\dots,r-1\}$ (three copies, or any larger number of copies per level, possibly different at different levels). If
--   $$\sum_{i,\gamma}\omega_{i,\gamma}y_{i,\gamma}\ge Q\iff\sum_{i,\gamma}2^iy_{i,\gamma}\ge Q\qquad\text{for every Boolean assignment }y=(y_{i,\gamma}),$$
--   then $\omega_{i,\gamma}=2^i$ for every level $i$ and copy $\gamma$.
--
--   It identifies the query coefficients of a common ramp in the proof of Lemma 4.11.
--
--   Differences from the source:
--   - generalization: three copies of every level; the conclusion also holds with any larger number of copies per level → one statement for k_i ≥ 3 copies at level i, the numbers k_i possibly different at different levels; reason: k_i = 3 is the first sentence and a common k_i > 3 the second (under either reading of "any larger number of copies per level"); the proof restricts to any three copies per level, which works for per-level counts
-- source:
--   Myrisiotis, The Complexity of ReLU Network Synthesis from a Parameter Multiset, arXiv:2611.04074v1, p. 24, Lemma 4.10

import Mathlib
import Definitions.Def_ReLUSynth_Boolean_Calibrated

namespace ReLUSynth.Boolean

/-- Lemma 4.10 (p. 24): let `Q = 2^r − 1` with `r ≥ 2`, and give positive integer weights to
`k_i ≥ 3` copies of every level `i ∈ {0, …, r − 1}` (three copies, or any larger number of copies
per level). If these weights with threshold `Q` give the same Boolean function as the weights
`2^i` with threshold `Q`, then every weight at level `i` is `2^i`. -/
theorem lemma_4_10 (r : ℕ) (k : Fin r → ℕ) (hr : 2 ≤ r) (hk : ∀ i, 3 ≤ k i)
    (ω : (i : Fin r) → Fin (k i) → ℕ) (hpos : ∀ i γ, 0 < ω i γ)
    (hsame : ∀ y : (i : Fin r) → Fin (k i) → Bool,
      (2 ^ r - 1 ≤ ∑ i, ∑ γ, ω i γ * (if y i γ then 1 else 0)) ↔
        (2 ^ r - 1 ≤ ∑ i, ∑ γ, 2 ^ i.val * (if y i γ then 1 else 0))) :
    ∀ i γ, ω i γ = 2 ^ i.val := by sorry

end ReLUSynth.Boolean
