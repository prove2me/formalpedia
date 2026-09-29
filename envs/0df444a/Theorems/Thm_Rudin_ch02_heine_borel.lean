-- Prove2me | Theorems.Thm_Rudin_ch02_heine_borel
-- name    : Rudin.ch02_heine_borel
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T18:55:48.53766+00:00
-- url     : https://prove2.me/theorems/77c53937-bbd0-4f85-bdb4-fd4c54710001
-- title:
--   Theorem 2.41 — Heine–Borel in $\mathbb{R}^k$
-- statement:
--   For a set $E$ in $\mathbb{R}^k$ the following three properties are equivalent: (a) $E$ is closed and bounded; (b) $E$ is compact; (c) every infinite subset of $E$ has a limit point in $E$. Rudin notes that (b) and (c) are equivalent in every metric space, while the equivalence with (a) is special to $\mathbb{R}^k$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 2, p. 40, Theorem 2.41

import Mathlib
import Definitions.Def_Rudin_ch02_topology

namespace Rudin

/-- Rudin, Theorem 2.41 (Heine–Borel): for a set `E` in `ℝ^k` the following are equivalent:
`E` is closed and bounded; `E` is compact; every infinite subset of `E` has a limit point
in `E`. -/
theorem ch02_heine_borel (k : ℕ) (E : Set (EuclideanSpace ℝ (Fin k))) :
    [IsClosed E ∧ Bornology.IsBounded E,
      IsCompact E,
      ∀ S ⊆ E, S.Infinite → ∃ p ∈ E, IsLimitPoint p S].TFAE := by sorry

end Rudin
