-- Prove2me | Theorems.Thm_SeymourMFMC_Binary_arrow_circuit
-- name    : SeymourMFMC.Binary.arrow_circuit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T04:47:21.748897+00:00
-- url     : https://prove2.me/theorems/87b247c2-fe36-4ee0-aa96-70c8e0484918
-- title:
--   (4.4) — in a critical MBC, x → y yields a circuit C ∋ x, y with |C| ≥ 3
-- statement:
--   Let $\mathbf L$ be a critical Mengerian binary clutter and $x \to y$. Then there is a circuit $C$ of $\mathbf L$ such that
--
--   1. $x, y \in C$;
--   2. $|C| \ge 3$;
--   3. if $z \in C - \{y\}$, then $z \to y$;
--   4. if $B \in b(\mathbf L)$, then
--   $$
--   |B - (C - \{y\})| \ge \tau(\mathbf L) - 1 .
--   $$
--
--   This circuit is the building block for (4.5), which produces circuits through a non-initial element whose other elements are initial.
--
--   **Formalization Note** (4) is stated additively as $\tau(\mathbf L) \le |B - (C - \{y\})| + 1$, which is equivalent over the integers and avoids truncated natural-number subtraction.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 207, (4.4)

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_blocker
import Definitions.Def_SeymourMFMC_Binary_IsClutter
import Definitions.Def_SeymourMFMC_Binary_IsBinary
import Definitions.Def_SeymourMFMC_Binary_IsMengerian
import Definitions.Def_SeymourMFMC_Binary_IsCritical
import Definitions.Def_SeymourMFMC_Binary_IsCircuit
import Definitions.Def_SeymourMFMC_Binary_tau
import Definitions.Def_SeymourMFMC_Binary_Arrow

namespace SeymourMFMC.Binary

/-- Seymour 1977, (4.4), p. 207: if `L` is a critical Mengerian binary clutter and `x → y`, then
there is a circuit `C` of `L` such that (i) `x, y ∈ C`, (ii) `|C| ≥ 3`, (iii) `z → y` for every
`z ∈ C − {y}`, and (iv) `|B − (C − {y})| ≥ τ(L) − 1` for every `B ∈ b(L)` (stated additively as
`τ(L) ≤ |B − (C − {y})| + 1`). -/
theorem arrow_circuit {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : IsClutter L) (hbin : IsBinary L) (hM : IsMengerian L) (hcrit : IsCritical L)
    (x y : α) (hxy : Arrow L x y) :
    ∃ C : Finset α, IsCircuit L C ∧ x ∈ C ∧ y ∈ C ∧ 3 ≤ C.card ∧
      (∀ z ∈ C.erase y, Arrow L z y) ∧
      ∀ B ∈ blocker L, tau L ≤ (B \ C.erase y).card + 1 := by sorry

end SeymourMFMC.Binary
