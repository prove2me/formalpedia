-- Prove2me | Theorems.Thm_Rudin_ch02_kcell_compact
-- name    : Rudin.ch02_kcell_compact
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:51:32.668906+00:00
-- url     : https://prove2.me/theorems/a03058cd-e46f-4bf3-ba9b-23b7e1a68eaa
-- title:
--   Theorem 2.40 — every $k$-cell is compact
-- statement:
--   Every $k$-cell $\{x \in \mathbb{R}^k : a_j \le x_j \le b_j\}$ is compact.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 2, p. 39, Theorem 2.40

import Mathlib
import Definitions.Def_Rudin_ch02_topology

namespace Rudin

/-- Rudin, Theorem 2.40: every `k`-cell is compact. -/
theorem ch02_kcell_compact (k : ℕ) (a b : Fin k → ℝ) : IsCompact (kCell k a b) := by sorry

end Rudin
