-- Prove2me | Theorems.Thm_Rudin_ch02_binary_sequences_uncountable
-- name    : Rudin.ch02_binary_sequences_uncountable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:45:34.756806+00:00
-- url     : https://prove2.me/theorems/227d06b3-9153-4a1c-b4e8-e59f4bbeb7f3
-- title:
--   Theorem 2.14 — the set of binary sequences is uncountable
-- statement:
--   The set of all sequences whose terms are the digits $0$ and $1$ is uncountable. Rudin proves this by Cantor's diagonal process; with Theorem 2.12 it separates the countable from the uncountable in the chapter.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 2, p. 30, Theorem 2.14

import Mathlib

namespace Rudin

/-- Rudin, Theorem 2.14: the set of all sequences whose terms are the digits `0` and `1` is
uncountable. -/
theorem ch02_binary_sequences_uncountable : ¬ (Set.univ : Set (ℕ → Fin 2)).Countable := by sorry

end Rudin
