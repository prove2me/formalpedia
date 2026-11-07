-- Prove2me | Theorems.Thm_SetMultCost_fact_5_2
-- name    : SetMultCost.fact_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:00.864224+00:00
-- url     : https://prove2.me/theorems/bc1a1bdc-342d-4386-967e-57fa71690be3
-- title:
--   Fact 5.2 — best approximation by convergents
-- statement:
--   Let $\alpha$ have the infinite continued fraction with convergents $p_k/q_k$. For every $k$, every $p\in\mathbb Z$ and every $q_k\le q<q_{k+1}$,
--
--   $$|q\alpha-p|\ge|q_k\alpha-p_k|.$$
--
--   Furthermore, for every $k$,
--
--   $$\frac{1}{q_k+q_{k+1}}\le|q_k\alpha-p_k|\le\frac{1}{q_{k+1}}.$$
--
--   This is the classical law of best approximation of the second kind, quoted from Schmidt's book.
--
--   Differences from the source:
--   - reading: "every k", for α with continued fraction [a₀, a₁, …] → `IsCFValue`, an infinite expansion with a_i ≥ 1 for i ≥ 1; reason: Definition 5.1 indexes the convergents by all i ∈ ℕ and writes the expansion without end, so "every k ∈ ℕ" is about infinite expansions (irrational α); α̃ is of this kind
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Fact 5.2, pp.16–17

import Mathlib
import Definitions.Def_SetMultCost_cfDen

namespace SetMultCost

/-- **Fact 5.2.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), pp.16–17: "Fix an arbitrary k ∈ N. For every p ∈ Z and for every qk ≤ q <
qk+1, the value |qα − p| is minimized at (pk, qk), i.e., |qα − p| ≥ |qkα − pk|. Furthermore, for every
k ∈ N, we have, 1/(qk + qk+1) ≤ |qkα − pk| ≤ 1/qk+1."

**Formalization Note.** "Every `k`" means an infinite expansion, `IsCFValue`. At `k = 0`, `a₁ = 1` the
range for `q` is empty. -/
theorem fact_5_2 (a : ℕ → ℤ) (α : ℝ) (h : IsCFValue a α) :
    (∀ (k : ℕ) (p q : ℤ), cfDen a k ≤ q → q < cfDen a (k + 1) →
      |(cfDen a k : ℝ) * α - (cfNum a k : ℝ)| ≤ |(q : ℝ) * α - (p : ℝ)|) ∧
    ∀ k : ℕ, 1 / ((cfDen a k : ℝ) + (cfDen a (k + 1) : ℝ)) ≤
        |(cfDen a k : ℝ) * α - (cfNum a k : ℝ)| ∧
      |(cfDen a k : ℝ) * α - (cfNum a k : ℝ)| ≤ 1 / (cfDen a (k + 1) : ℝ) := by sorry

end SetMultCost
