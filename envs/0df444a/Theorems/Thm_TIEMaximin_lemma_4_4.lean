-- Prove2me | Theorems.Thm_TIEMaximin_lemma_4_4
-- name    : TIEMaximin.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:39:16.931065+00:00
-- url     : https://prove2.me/theorems/fb04c908-6099-4fd8-a979-c9555307c436
-- title:
--   Lemma 4.4 — completing the marginals
-- statement:
--   If a finite lottery of integral suballocations has mean $\bar b\le x$ coordinatewise and $x$ is complete (nonnegative entries, every column summing to one), then it can be extended to a finite lottery of complete allocations with mean $x$, without removing any earlier assignment.
--
--   This is the fourth step of the mechanism. Completion only adds goods, so it never lowers a nonnegative value.
--
--   Differences from the source:
--   - encoding: it can be extended to a lottery of complete allocations → a kernel κ with the lottery `μ'.bind κ`, every outcome of `κ A'` extending `A'` on the support; reason: same extensions
--   - encoding: finite lottery → `PMF` on a finite type, expectations as finite sums; reason: a distribution on a finite type is finite; same instances
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Lemma 4.4, p.22

import Mathlib
import Definitions.Def_TIEMaximin_Basic

namespace TIEMaximin

/-- **Lemma 4.4** (p.22). If a finite lottery of integral suballocations has mean `b̄ ≤ x`
coordinatewise and `x` is complete, it can be extended to a finite lottery of complete allocations
with mean `x`, without removing any earlier assignment.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Lemma 4.4, p.22.

**Formalization Note.** The extension is a kernel `κ`; the extended lottery is `μ'.bind κ`.
"Complete" for a fractional allocation is nonnegative entries with column sums one (§2, p.6). -/
theorem lemma_4_4 {n m : ℕ} (μ' : PMF (SubAlloc n m)) (x : Fin n → Fin m → ℝ)
    (hx0 : ∀ i g, 0 ≤ x i g) (hx1 : ∀ g, ∑ i, x i g = 1)
    (hb : ∀ i g, subMarginal μ' i g ≤ x i g) :
    ∃ κ : SubAlloc n m → PMF (Alloc n m),
      (∀ A' ∈ μ'.support, ∀ A ∈ (κ A').support, ∀ g i, A' g = some i → A g = i) ∧
      Implements (μ'.bind κ) x := by sorry

end TIEMaximin
