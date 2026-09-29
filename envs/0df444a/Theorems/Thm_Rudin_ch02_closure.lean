-- Prove2me | Theorems.Thm_Rudin_ch02_closure
-- name    : Rudin.ch02_closure
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:46:40.713456+00:00
-- url     : https://prove2.me/theorems/188f8446-8a3f-4cf8-aa7d-a89e8b29455f
-- title:
--   Theorem 2.27 — the closure is the smallest closed superset
-- statement:
--   For $E$ in a metric space $X$: the closure of $E$ is $E \cup E'$, where $E'$ is the set of limit points of $E$; the closure is closed; the closure equals $E$ exactly when $E$ is closed; and the closure is contained in every closed set containing $E$. Hence $\bar E$ is the smallest closed subset of $X$ containing $E$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 2, p. 35, Definition 2.26 and Theorem 2.27

import Mathlib
import Definitions.Def_Rudin_ch02_topology

namespace Rudin

/-- Rudin, Definition 2.26 and Theorem 2.27: the closure of `E` is `E` together with its limit
points; it is closed; it equals `E` exactly when `E` is closed; and it is contained in every
closed set containing `E`, so it is the smallest closed set containing `E`. -/
theorem ch02_closure {X : Type*} [MetricSpace X] (E : Set X) :
    closure E = E ∪ {p | IsLimitPoint p E} ∧
    IsClosed (closure E) ∧
    (closure E = E ↔ IsClosed E) ∧
    (∀ F : Set X, IsClosed F → E ⊆ F → closure E ⊆ F) := by sorry

end Rudin
