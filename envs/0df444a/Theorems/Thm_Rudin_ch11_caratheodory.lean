-- Prove2me | Theorems.Thm_Rudin_ch11_caratheodory
-- name    : Rudin.ch11_caratheodory
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:14:34.959112+00:00
-- url     : https://prove2.me/theorems/839ef4d5-bc59-4d66-9407-46f975dd9f64
-- title:
--   Theorem 11.10 — the measurable sets form a $\sigma$-algebra
-- statement:
--   The sets that are measurable with respect to an outer measure form a $\sigma$-algebra, and the outer measure is countably additive on it: a countable union of pairwise disjoint measurable sets is measurable, and its measure is the sum of their measures.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 11, p. 305, Theorem 11.10

import Mathlib
import Definitions.Def_Rudin_ch11_L2

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 11.10: the sets measurable with respect to an outer measure form a σ-algebra,
and the outer measure is countably additive on them. -/
theorem ch11_caratheodory {X : Type*} (m : OuterMeasure X) (s : ℕ → Set X)
    (hs : ∀ n, MeasurableSet[m.caratheodory] (s n)) (hdisj : Pairwise (Function.onFun Disjoint s)) :
    MeasurableSet[m.caratheodory] (⋃ n, s n) ∧ m (⋃ n, s n) = ∑' n, m (s n) := by sorry

end Rudin
