-- Prove2me | Theorems.Thm_Rudin_ch02_perfect_uncountable
-- name    : Rudin.ch02_perfect_uncountable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:52:33.654765+00:00
-- url     : https://prove2.me/theorems/a0c4cbc5-f7db-4fa1-8d6d-5d40a18df768
-- title:
--   Theorem 2.43 — nonempty perfect sets are uncountable
-- statement:
--   A nonempty perfect set $P \subseteq \mathbb{R}^k$ — closed, with every point a limit point of $P$ — is uncountable. In particular every interval $[a,b]$ with $a < b$ is uncountable, and so is the Cantor set.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 2, p. 41, Theorem 2.43

import Mathlib

namespace Rudin

/-- Rudin, Theorem 2.43: a nonempty perfect set in `ℝ^k` — a nonempty closed set every point of
which is a limit point of the set — is uncountable. -/
theorem ch02_perfect_uncountable (k : ℕ) (P : Set (EuclideanSpace ℝ (Fin k)))
    (hne : P.Nonempty) (hP : Perfect P) : ¬ P.Countable := by sorry

end Rudin
