-- Prove2me | Theorems.Thm_SetMultCost_lemma_5_3
-- name    : SetMultCost.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:05.299663+00:00
-- url     : https://prove2.me/theorems/12624196-5b92-44cb-9b00-b53a8e9f617f
-- title:
--   Lemma 5.3 — approximation gets worse linearly
-- statement:
--   Let $\alpha$ have the infinite continued fraction with convergents $p_k/q_k$. For every $k$, every $p\in\mathbb Z$, and every positive integer $q\le2q_{k+1}/3$,
--
--   $$|q\alpha-p|\ge q\cdot\frac{1}{2q_kq_{k+1}}.$$
--
--   So, up to $2q_{k+1}/3$, the approximation gets worse as $q$ grows, on the scale $1/(2q_kq_{k+1})$. This is the arithmetic heart of the threshold construction.
--
--   Differences from the source:
--   - reading: "Fix an arbitrary k ∈ N" for α with its convergents → `IsCFValue`, an infinite expansion; reason: as in Fact 5.2
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Lemma 5.3, p.17

import Mathlib
import Definitions.Def_SetMultCost_cfDen

namespace SetMultCost

/-- **Lemma 5.3 (Main Technical Lemma).** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), p.17: "Fix an arbitrary k ∈ N. For every p ∈ Z and
for every q ∈ N>0 with q ≤ 2qk+1/3, we have, |qα − p| ≥ q · 1/(2qkqk+1)". -/
theorem lemma_5_3 (a : ℕ → ℤ) (α : ℝ) (h : IsCFValue a α) (k : ℕ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hqk : 3 * (q : ℤ) ≤ 2 * cfDen a (k + 1)) :
    (q : ℝ) * (1 / (2 * (cfDen a k : ℝ) * (cfDen a (k + 1) : ℝ))) ≤ |(q : ℝ) * α - (p : ℝ)| := by sorry

end SetMultCost
