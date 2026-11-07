-- Prove2me | Theorems.Thm_RandOrderSort_lemma_4_11
-- name    : RandOrderSort.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:44.054952+00:00
-- url     : https://prove2.me/theorems/b22558be-3fa3-4fb6-b355-9470ef6abd8e
-- title:
--   Lemma 4.11 — geometrically weighted fixed-partition errors
-- statement:
--   Let $n\ge 8192$ and $q\in(0,1)$. The variable
--   $$D_{\mathrm{err}}=4\kappa\sum_{\nu\in\{2,4,\dots,b\}}\nu\mathbf 1[\mathrm{Bad}_\nu]$$
--   dominates all bad-parent charges in nonfinal shrinking arrivals and subsequent nonfinal bucket-merging reallocations. There are absolute constants $\theta_b>0$ and $M_b\ge 1$ such that, uniformly in $q$ and $n$,
--   $$\mathbb E[e^{\theta_bD_{\mathrm{err}}}]\le M_b.$$
--
--   An inaccurate interval covering $\nu$ of the finest buckets thus costs $O(\nu)$ in total across the merging phases, rather than $O(\nu\log n)$.
--
--   **Formalization Note** Domination is stated for every input vector with distinct values none equal to $q$. The charges are those of top-marked selected bad parents, in the arrival operations of phases $1,\dots,k-1$ and the reallocations at the start of phases $2,\dots,k-1$; nonselected top marks contribute zero (p.22).
--
--   Differences from the source:
--   - generalization: the domination, on the event of distinct keys in the i.i.d. experiment → for every input vector with distinct values none equal to q, not only those in [0,1]; reason: the deterministic inequality on the page's event is a special case
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Lemma 4.11, p.33, display (47)

import Mathlib
import Definitions.Def_RandOrderSort_Wi
open MeasureTheory

namespace RandOrderSort

/-- **Lemma 4.11 (Geometrically weighted fixed-partition errors)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.33: "The variable D_err in
(46) dominates all bad-parent charges in nonfinal shrinking arrivals and subsequent nonfinal
bucket-merging reallocations. There are absolute constants θ_b > 0 and M_b ≥ 1 such that, uniformly
in q and n, E[e^{θ_b D_err}] ≤ M_b. (47)"

**Formalization Note.** For `n ≥ 8192` and `q ∈ (0,1)`. Domination is deterministic, on the i.i.d.
run for every input vector with distinct values none equal to `q` (in particular almost surely): the
charges `Γ_q(v)` of top-marked selected bad parents in the arrival operations of shrinking phases
`1, …, k − 1` and in the reallocations at the start of phases `2, …, k − 1` sum to at most `D_err`
(`badCharges`). The moment bound is under `iidUnif n`, with `θ_b`, `M_b` chosen before `n` and `q`. -/
theorem lemma_4_11 :
    (∀ n, 16 * T ≤ n → ∀ q : ℝ, 0 < q → q < 1 → ∀ X : Fin n → ℝ, Function.Injective X →
      (∀ a, X a ≠ q) →
        ∑ i ∈ Finset.Icc 1 (k n - 1), badCharges X q i true +
            ∑ i ∈ Finset.Icc 2 (k n - 1), badCharges X q i false ≤ Derr (prefixOf X) q) ∧
    ∃ θb : ℝ, 0 < θb ∧ ∃ Mb' : ℝ, 1 ≤ Mb' ∧ ∀ n, 16 * T ≤ n → ∀ q : ℝ, 0 < q → q < 1 →
      Integrable (fun X : Fin n → ℝ => Real.exp (θb * Derr (prefixOf X) q)) (iidUnif n) ∧
      ∫ X, Real.exp (θb * Derr (prefixOf X) q) ∂(iidUnif n) ≤ Mb' := by sorry

end RandOrderSort
