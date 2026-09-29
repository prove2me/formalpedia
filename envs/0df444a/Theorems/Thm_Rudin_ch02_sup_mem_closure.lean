-- Prove2me | Theorems.Thm_Rudin_ch02_sup_mem_closure
-- name    : Rudin.ch02_sup_mem_closure
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:47:52.530985+00:00
-- url     : https://prove2.me/theorems/18aa1fb8-b18f-48e4-bc0e-b8719a3be3d6
-- title:
--   Theorem 2.28 — the supremum lies in the closure
-- statement:
--   If $E \subseteq \mathbb{R}$ is nonempty and bounded above, then $\sup E \in \bar E$; consequently $\sup E \in E$ whenever $E$ is closed.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 2, p. 35, Theorem 2.28

import Mathlib

namespace Rudin

/-- Rudin, Theorem 2.28: if `E` is a nonempty set of real numbers which is bounded above, then
`sup E` lies in the closure of `E`; hence `sup E ∈ E` if `E` is closed. -/
theorem ch02_sup_mem_closure (E : Set ℝ) (hne : E.Nonempty) (hbdd : BddAbove E) :
    sSup E ∈ closure E ∧ (IsClosed E → sSup E ∈ E) := by sorry

end Rudin
