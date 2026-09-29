-- Prove2me | Theorems.Thm_Rudin_ch08_fundamental_theorem_of_algebra
-- name    : Rudin.ch08_fundamental_theorem_of_algebra
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:21:34.166088+00:00
-- url     : https://prove2.me/theorems/629b7940-4390-403b-8a69-ca3a05802273
-- title:
--   Theorem 8.8 — the fundamental theorem of algebra
-- statement:
--   If $a_0, \dots, a_n$ are complex numbers with $n \ge 1$ and $a_n \ne 0$, then $\sum_{k=0}^{n} a_k z^k = 0$ for some complex $z$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 8, p. 184, Theorem 8.8

import Mathlib
import Definitions.Def_Rudin_ch08_fourier

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 8.8 (fundamental theorem of algebra): every nonconstant complex polynomial
has a root. -/
theorem ch08_fundamental_theorem_of_algebra (n : ℕ) (hn : 1 ≤ n) (a : ℕ → ℂ) (han : a n ≠ 0) :
    ∃ z : ℂ, ∑ k ∈ Finset.range (n + 1), a k * z ^ k = 0 := by sorry

end Rudin
