-- Prove2me | Theorems.Thm_SampleCRS_AlmostGreedy_Supplement_lemma_3_3
-- name    : SampleCRS.AlmostGreedy.Supplement.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:39:52.09449+00:00
-- url     : https://prove2.me/theorems/e13217c8-66ac-4e35-9a8e-9d9870a14f7e
-- title:
--   Lemma 3.3 — prefix threshold-product bound
-- statement:
--   Let $p\in[0,1]^n$ and fix an arrival $\ell$ whose prefix mass satisfies $\sum_{i=1}^{\ell}p_i\le1$. For the product $g_\ell(t)=\prod_{t<j<\ell}(1-p_j)$ when $t<\ell$, with $g_\ell(t)=0$ otherwise,
--   $$\sum_{i=1}^{\ell-1}p_i(1-p_i)\bigl(g_\ell(i)-g_\ell(0)\bigr)\le3/8.$$
--   There is no restriction on suffix mass and no total-mass-one assumption. This is the product inequality supporting the threshold-loss bound.
--
--   Differences from the source:
--   - encoding: elements 1,…,n and independent Bernoulli trials → Fin n and finite product-weight expectations; reason: the label shift is a bijection and the weights are exactly the independent Bernoulli law
--   - encoding: threshold 0 before all arrivals and thresholds 1,…,n → none and some i : Option (Fin n); reason: a separate sentinel preserves strict-after-threshold eligibility at the first arrival
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Lemma 3.3, p. 13

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_threshold

namespace SampleCRS.AlmostGreedy.Supplement

/-- Lemma 3.3, p.13. prefix threshold-product bound. -/
theorem lemma_3_3 {n : ℕ} (p : Fin n → ℝ) (hp : ValidProb p) (ell : Fin n)
    (hprefix : (∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ ell), p i) ≤ 1) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < ell),
      p i * (1 - p i) * (g p ell (some i) - g p ell none)) ≤ (3 / 8 : ℝ) := by sorry

end SampleCRS.AlmostGreedy.Supplement
