-- Prove2me | Theorems.Thm_SubmodOrder_thresholdAdd_value_ge
-- name    : SubmodOrder.thresholdAdd_value_ge
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:38:06.28848+00:00
-- url     : https://prove2.me/theorems/69af865c-84f9-470d-bb4f-4d94e9478f9d
-- title:
--   Proof of Theorem 2, p.21 — Threshold Add returns $|S|\le k$ with $f(S)\ge |S|\,\tau$
-- statement:
--   Let $f$ be a set function with $f(\emptyset)=0$, let $k$ be a cardinality and $\tau$ any threshold, and let $S$ be the output of Threshold Add$(k,\tau)$, with $k'=|S|$. Then
--
--   $$
--   k'\le k\qquad\text{and}\qquad f(S)\ \ge\ k'\,\tau .
--   $$
--
--   Each added element raised the value by at least $\tau$. In the proof of Theorem 2 this settles the case $k'=k$, where $k\tau\ge(1-\varepsilon)\frac12\mathrm{OPT}$.
--
--   Differences from the source:
--   - generalization: f monotone and subadditive with a weak submodular order, τ = τ_i a grid threshold of Algorithm 1 → every f with f(∅) = 0 and every real τ; reason: the bound uses only f(∅) = 0 and the test of Algorithm 2; it specializes to the paper's setting
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, proof of Theorem 2, p.21; Algorithm 2, p.13 ("Output: Set S of size at most k")

import Mathlib
import Definitions.Def_SubmodOrder_OracleProg
import Definitions.Def_SubmodOrder_thresholdAdd

namespace SubmodOrder

/-- Threshold Add gains `τ` per added element (Udwani, arXiv:2107.02743v5, proof of Theorem 2,
p.21: "Let k′ denote the cardinality of set S. By definition of Threshold Add, f(S) ≥ k′τ.").

For every set function `f` with `f(∅) = 0` and every threshold `τ`, the output `S` of
Threshold Add(k, τ) has `|S| ≤ k` (Algorithm 2: "Output: Set S of size at most k") and
`f(S) ≥ |S| · τ`.

**Formalization Note.** `OracleProg.run f (thresholdAdd π k τ)` is the pair `(S, f(S))` returned
by the program; `S` is its first component. -/
theorem thresholdAdd_value_ge {α : Type*} [DecidableEq α] {n : ℕ} (π : α ≃ Fin n) (k : ℕ)
    (τ : ℝ) (f : Finset α → ℝ) (hf0 : f ∅ = 0) :
    (OracleProg.run f (thresholdAdd π k τ)).1.card ≤ k ∧
      ((OracleProg.run f (thresholdAdd π k τ)).1.card : ℝ) * τ ≤
        f (OracleProg.run f (thresholdAdd π k τ)).1 := by sorry

end SubmodOrder
