-- Prove2me | Theorems.Thm_Rudin_ch03_mertens
-- name    : Rudin.ch03_mertens
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T19:29:02.099055+00:00
-- url     : https://prove2.me/theorems/df5638fc-c576-4368-a934-1fb816fdd3f1
-- title:
--   Theorem 3.50 — Mertens' theorem on Cauchy products
-- statement:
--   Suppose $\sum a_n$ converges absolutely to $A$, $\sum b_n$ converges to $B$, and $c_n = \sum_{k=0}^{n} a_k b_{n-k}$. Then $\sum c_n$ converges to $AB$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 3, p. 74, Theorem 3.50

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 3.50 (Mertens): if `∑ aₙ` converges absolutely to `A`, `∑ bₙ` converges to
`B`, and `cₙ = ∑_{k ≤ n} aₖ bₙ₋ₖ`, then `∑ cₙ` converges to `A B`. -/
theorem ch03_mertens (a b : ℕ → ℂ) (A B : ℂ)
    (habs : SeriesConvergesAbsolutely a) (hA : SeriesConvergesTo a A)
    (hB : SeriesConvergesTo b B) :
    SeriesConvergesTo (fun n => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)) (A * B) := by sorry

end Rudin
