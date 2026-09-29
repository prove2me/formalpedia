-- Prove2me | Theorems.Thm_Rudin_ch02_countable_union
-- name    : Rudin.ch02_countable_union
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:44:56.600974+00:00
-- url     : https://prove2.me/theorems/edf94433-c302-4b8a-89c3-c6b84d6fc904
-- title:
--   Theorem 2.12 — a countable union of countable sets is countable
-- statement:
--   If $E_1, E_2, \dots$ is a sequence of countable sets, then $\bigcup_{n} E_n$ is countable. (Rudin's 'countable' allows finite sets, which is Mathlib's `Set.Countable`.)
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 2, p. 29, Theorem 2.12

import Mathlib

namespace Rudin

/-- Rudin, Theorem 2.12: the union of a sequence of countable sets is countable. -/
theorem ch02_countable_union {X : Type*} (E : ℕ → Set X) (h : ∀ n, (E n).Countable) :
    (⋃ n, E n).Countable := by sorry

end Rudin
