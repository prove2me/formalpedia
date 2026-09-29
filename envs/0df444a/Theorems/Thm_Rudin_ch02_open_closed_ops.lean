-- Prove2me | Theorems.Thm_Rudin_ch02_open_closed_ops
-- name    : Rudin.ch02_open_closed_ops
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:45:52.81792+00:00
-- url     : https://prove2.me/theorems/7faae526-cd5e-4a22-adb1-44870ab23241
-- title:
--   Theorem 2.24 — unions and intersections of open and closed sets
-- statement:
--   In a metric space: (a) any union of open sets is open; (b) any intersection of closed sets is closed; (c) a finite intersection of open sets is open; (d) a finite union of closed sets is closed. The finiteness in (c) and (d) is essential, as Rudin's Example 2.25 shows.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 2, p. 34, Theorem 2.24

import Mathlib

namespace Rudin

/-- Rudin, Theorem 2.24: arbitrary unions of open sets are open, arbitrary intersections of
closed sets are closed, finite intersections of open sets are open, and finite unions of closed
sets are closed. -/
theorem ch02_open_closed_ops (X : Type) [MetricSpace X] :
    (∀ (ι : Type) (G : ι → Set X), (∀ i, IsOpen (G i)) → IsOpen (⋃ i, G i)) ∧
    (∀ (ι : Type) (F : ι → Set X), (∀ i, IsClosed (F i)) → IsClosed (⋂ i, F i)) ∧
    (∀ (n : ℕ) (G : Fin n → Set X), (∀ i, IsOpen (G i)) → IsOpen (⋂ i, G i)) ∧
    (∀ (n : ℕ) (F : Fin n → Set X), (∀ i, IsClosed (F i)) → IsClosed (⋃ i, F i)) := by sorry

end Rudin
