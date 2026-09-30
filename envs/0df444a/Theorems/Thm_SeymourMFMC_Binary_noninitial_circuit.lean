-- Prove2me | Theorems.Thm_SeymourMFMC_Binary_noninitial_circuit
-- name    : SeymourMFMC.Binary.noninitial_circuit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T04:56:06.424863+00:00
-- url     : https://prove2.me/theorems/cadad3c0-dce2-4f0c-9f5b-6496bdc477aa
-- title:
--   (4.5) — a non-initial element of a critical MBC lies on a circuit of initial elements
-- statement:
--   Let $\mathbf L$ be a critical Mengerian binary clutter and let $x \in E(\mathbf L)$ be not initial. Then there is a circuit $C$ of $\mathbf L$ such that
--
--   1. $x \in C$;
--   2. all other members of $C$ are initial;
--   3. if $y \in C - \{x\}$ then $y \to x$;
--   4. $|C| \ge 3$;
--   5. if $B \in mb(\mathbf L)$ then
--   $$
--   |B \cap (C - \{x\})| \le 1 .
--   $$
--
--   The paper calls this result crucial. It gives (4.6), and it is used again at step (5.28) of the proof of the main theorem.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 207, (4.5)

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_ground
import Definitions.Def_SeymourMFMC_Binary_IsClutter
import Definitions.Def_SeymourMFMC_Binary_IsBinary
import Definitions.Def_SeymourMFMC_Binary_IsMengerian
import Definitions.Def_SeymourMFMC_Binary_IsCritical
import Definitions.Def_SeymourMFMC_Binary_IsCircuit
import Definitions.Def_SeymourMFMC_Binary_mb
import Definitions.Def_SeymourMFMC_Binary_Arrow
import Definitions.Def_SeymourMFMC_Binary_IsInitial

namespace SeymourMFMC.Binary

/-- Seymour 1977, (4.5), p. 207: if `L` is a critical Mengerian binary clutter and `x ∈ E(L)` is
not initial, then there is a circuit `C` of `L` such that (i) `x ∈ C`, (ii) all other members of
`C` are initial, (iii) `y → x` for every `y ∈ C − {x}`, (iv) `|C| ≥ 3`, and
(v) `|B ∩ (C − {x})| ≤ 1` for every `B ∈ mb(L)`. -/
theorem noninitial_circuit {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : IsClutter L) (hbin : IsBinary L) (hM : IsMengerian L) (hcrit : IsCritical L)
    (x : α) (hx : x ∈ ground L) (hni : ¬ IsInitial L x) :
    ∃ C : Finset α, IsCircuit L C ∧ x ∈ C ∧ (∀ y ∈ C.erase x, IsInitial L y) ∧
      (∀ y ∈ C.erase x, Arrow L y x) ∧ 3 ≤ C.card ∧
      ∀ B ∈ mb L, (B ∩ C.erase x).card ≤ 1 := by sorry

end SeymourMFMC.Binary
