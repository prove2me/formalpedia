-- Prove2me | Theorems.Thm_TIEMaximin_appendix_A_3
-- name    : TIEMaximin.appendix_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:39:09.22308+00:00
-- url     : https://prove2.me/theorems/3c300c1f-e9f9-4ada-8a95-cd419317c5f3
-- title:
--   Appendix A.3 — support reduction to $m(n-1)+1$ allocations (running time in the goal)
-- statement:
--   Let $n\ge1$. Every lottery over complete allocations of $m$ goods to $n$ agents can be replaced by a lottery whose support is contained in the original support, has at most $m(n-1)+1$ allocations, and has the same mean matrix.
--
--   Since the support only shrinks, every ex-post guarantee is preserved, and since the mean is unchanged, so are the ex-ante guarantees.
--
--   Differences from the source:
--   - generalization: the explicit lottery (rational weights, more than m(n − 1) + 1 support points) → every `PMF` on allocations with real weights; reason: the explicit lottery is an instance; the case of a small support is trivial
--   - reading: these rational linear-algebra steps take polynomial time → carried by `theorem_1_1`; reason: the running time needs the machine of the goal; this item states the combinatorial reduction
--   - encoding: n agents → `0 < n`, so `n - 1` is not truncated; reason: no allocation exists for n = 0 < m
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Appendix A.3, p.39

import Mathlib
import Definitions.Def_TIEMaximin_Basic

namespace TIEMaximin

/-- **Appendix A.3, support reduction** (p.39). Every lottery over complete allocations has a
sub-lottery with at most `m(n − 1) + 1` support points, supported inside the original support,
with the same mean matrix.

arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…, Appendix A.3, p.39.

**Formalization Note.** `0 < n`, so `n - 1` is not truncated. The weights are real. That the steps
are rational linear algebra in polynomial time is carried by `theorem_1_1`. -/
theorem appendix_A_3 {n m : ℕ} (hn : 0 < n) (μ : PMF (Alloc n m)) :
    ∃ μ' : PMF (Alloc n m),
      μ'.support ⊆ μ.support ∧ μ'.support.ncard ≤ m * (n - 1) + 1 ∧
      ∀ i g, marginal μ' i g = marginal μ i g := by sorry

end TIEMaximin
