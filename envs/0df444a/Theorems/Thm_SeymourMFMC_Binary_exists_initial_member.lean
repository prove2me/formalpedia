-- Prove2me | Theorems.Thm_SeymourMFMC_Binary_exists_initial_member
-- name    : SeymourMFMC.Binary.exists_initial_member
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T05:03:15.41933+00:00
-- url     : https://prove2.me/theorems/a6aa8f82-ab7d-4564-a701-bc75868d9496
-- title:
--   (4.6) — a nontrivial critical MBC has a member consisting of initial elements
-- statement:
--   Let $\mathbf L$ be a nontrivial ($\mathbf L \neq \emptyset$, $\mathbf L \neq \{\emptyset\}$) critical Mengerian binary clutter. Then there exists $A \in \mathbf L$ such that each member of $A$ is initial:
--
--   $$
--   \exists A \in \mathbf L\ \ \forall a \in A:\ a \text{ is initial}.
--   $$
--
--   $Q_6$ has no initial element, and this contrast is what the proof of the main theorem exploits, at step (5.19).
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 208, (4.6)

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_IsClutter
import Definitions.Def_SeymourMFMC_Binary_IsBinary
import Definitions.Def_SeymourMFMC_Binary_IsMengerian
import Definitions.Def_SeymourMFMC_Binary_IsCritical
import Definitions.Def_SeymourMFMC_Binary_IsNontrivial
import Definitions.Def_SeymourMFMC_Binary_IsInitial

namespace SeymourMFMC.Binary

/-- Seymour 1977, (4.6), p. 208: if `L` is a nontrivial critical Mengerian binary clutter, then
there exists `A ∈ L` such that each member of `A` is initial. -/
theorem exists_initial_member {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : IsClutter L) (hbin : IsBinary L) (hM : IsMengerian L) (hcrit : IsCritical L)
    (hnt : IsNontrivial L) :
    ∃ A ∈ L, ∀ a ∈ A, IsInitial L a := by sorry

end SeymourMFMC.Binary
