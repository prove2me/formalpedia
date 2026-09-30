-- Prove2me | Theorems.Thm_SeymourMFMC_Binary_circuit_card_ge_two
-- name    : SeymourMFMC.Binary.circuit_card_ge_two
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T04:14:55.629429+00:00
-- url     : https://prove2.me/theorems/bec285d0-0267-40c3-88fd-14b931309ebb
-- title:
--   (3.6)(i) — circuits of a binary clutter have at least 2 elements
-- statement:
--   Let $\mathbf L$ be a binary clutter. Every circuit $C$ of $\mathbf L$ (a minimal nonempty subset of $E(\mathbf L)$ with even intersection with each member of $b(\mathbf L)$) satisfies
--
--   $$
--   |C| \ge 2 .
--   $$
--
--   So a binary clutter has no loops, and parallel pairs $\{x, y\}$ are the smallest possible circuits.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 202, (3.6)(i)

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_IsClutter
import Definitions.Def_SeymourMFMC_Binary_IsBinary
import Definitions.Def_SeymourMFMC_Binary_IsCircuit

namespace SeymourMFMC.Binary

/-- Seymour 1977, (3.6)(i), p. 202: all circuits of a binary clutter have cardinality at
least 2. -/
theorem circuit_card_ge_two {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : IsClutter L) (hbin : IsBinary L) (C : Finset α) (hC : IsCircuit L C) :
    2 ≤ C.card := by sorry

end SeymourMFMC.Binary
