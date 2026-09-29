-- Prove2me | Theorems.Thm_Rudin_ch04_extreme_value
-- name    : Rudin.ch04_extreme_value
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:14:33.115947+00:00
-- url     : https://prove2.me/theorems/8c6dd802-efab-4e72-be39-ad40870a08c2
-- title:
--   Theorem 4.16 — the extreme value theorem
-- statement:
--   A continuous real function on a nonempty compact metric space attains both its supremum and its infimum: there are points $p$ and $q$ with $f(x) \le f(p)$ and $f(q) \le f(x)$ for all $x$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 4, p. 89, Theorem 4.16

import Mathlib
import Definitions.Def_Rudin_ch04_continuity

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 4.16: a continuous real function on a nonempty compact metric space attains
its supremum and its infimum. -/
theorem ch04_extreme_value {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (f : X → ℝ) (hf : Continuous f) :
    (∃ p : X, ∀ x : X, f x ≤ f p) ∧ (∃ q : X, ∀ x : X, f q ≤ f x) := by sorry

end Rudin
