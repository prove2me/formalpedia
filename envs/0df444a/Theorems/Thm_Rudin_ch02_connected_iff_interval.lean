-- Prove2me | Theorems.Thm_Rudin_ch02_connected_iff_interval
-- name    : Rudin.ch02_connected_iff_interval
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:54:16.637403+00:00
-- url     : https://prove2.me/theorems/814f06ba-18fe-4023-889a-f40fa0b24799
-- title:
--   Theorem 2.47 — connected subsets of the line
-- statement:
--   A subset $E$ of $\mathbb{R}$ is connected if and only if it is order-convex: whenever $x, y \in E$ and $x < z < y$, also $z \in E$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 2, p. 42, Theorem 2.47

import Mathlib

namespace Rudin

/-- Rudin, Theorem 2.47: a subset `E` of the real line is connected if and only if it is
order-convex: whenever `x, y ∈ E` and `x < z < y`, also `z ∈ E`. -/
theorem ch02_connected_iff_interval (E : Set ℝ) :
    IsPreconnected E ↔ ∀ x ∈ E, ∀ y ∈ E, ∀ z : ℝ, x < z → z < y → z ∈ E := by sorry

end Rudin
