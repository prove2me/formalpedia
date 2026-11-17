-- Prove2me | Theorems.Thm_SparseHistComm_Supplement_theorem_4
-- name    : SparseHistComm.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:44:16.306306+00:00
-- url     : https://prove2.me/theorems/7a4775a2-2b62-4c9f-8045-342edf713c7c
-- title:
--   Theorem 4 — when homogeneity has no leading cost
-- statement:
--   For every $n\ge1$, $k\ge1$, $0\le D<k$, and $0\le\delta<1$,
--
--   $$
--   1\le
--   \frac{\Lambda_{n,k,D}(\delta)}{(1-\delta)(nk-\lfloor nD\rfloor)}
--   \le \frac{n(k-\lfloor D\rfloor)}{nk-\lfloor nD\rfloor}
--   \le n.
--   $$
--
--   Furthermore,
--
--   $$
--   \Lambda_{n,k,D}(\delta)=(1-\delta)(nk-\lfloor nD\rfloor)
--   \quad\Longleftrightarrow\quad
--   \lfloor nD\rfloor=n\lfloor D\rfloor.
--   $$
--
--   The theorem exactly identifies when a common encoder has no additional leading communication cost.
--
--   Differences from the source:
--   - encoding: the paper's floors and quotient are implicit real arithmetic → `Int.floor` and ordinary real division, with positivity supplied by the theorem's standing assumptions; reason: the same denominators are strictly positive on every source instance
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Theorem 4, p.9; proof p.19

import Mathlib
import Definitions.Def_SparseHistComm_Lambda
import Definitions.Def_SparseHistComm_threshold

namespace SparseHistComm

namespace Supplement

/-- **Theorem 4 (When homogeneity has no leading cost)** (Ye–Fan, *Optimal Communication for
Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256
29df82a4…f27c6f), p.9). This is the complete ratio chain and the equality criterion in both
directions.

**Formalization Note** The standing assumptions make the two denominators strictly positive;
division is ordinary real division. -/
theorem theorem_4 (n k : ℕ) (D δ : ℝ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hD0 : 0 ≤ D) (hDk : D < k)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    1 ≤ Lambda n k D δ / ((1 - δ) * (threshold n k D : ℝ)) ∧
    Lambda n k D δ / ((1 - δ) * (threshold n k D : ℝ)) ≤
      (n : ℝ) * (k - ⌊D⌋) / (threshold n k D : ℝ) ∧
    (n : ℝ) * (k - ⌊D⌋) / (threshold n k D : ℝ) ≤ n ∧
    (Lambda n k D δ = (1 - δ) * (threshold n k D : ℝ) ↔
      ⌊(n : ℝ) * D⌋ = (n : ℤ) * ⌊D⌋) := by sorry

end Supplement

end SparseHistComm
