-- Prove2me | Theorems.Thm_SeymourMFMC_Binary_theorem_mengerian_iff_no_Q6_minor
-- name    : SeymourMFMC.Binary.theorem_mengerian_iff_no_Q6_minor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T05:19:45.175898+00:00
-- url     : https://prove2.me/theorems/d9834952-24ae-4650-8d22-c615066d6904
-- title:
--   Seymour's theorem — a binary clutter is Mengerian iff it has no Q₆ minor
-- statement:
--   Let $\mathbf L$ be a binary clutter: a clutter in which every member meets every member of the blocker $b(\mathbf L)$ in an odd number of elements. Then
--
--   $$
--   \mathbf L \text{ is Mengerian} \iff \mathbf L \text{ has no minor isomorphic to } Q_6,
--   $$
--
--   where $Q_6 = \{\{1,3,5\},\{1,4,6\},\{2,3,6\},\{2,4,5\}\}$. Being Mengerian means that for every nonnegative integer weighting $w$ of $E(\mathbf L)$ the maximum integral packing of members of $\mathbf L$ under capacities $w$ equals the minimum $w$-weight of a member of $b(\mathbf L)$ (with the convention that $\{\emptyset\}$ is Mengerian).
--
--   The edge sets of the $u$–$v$ paths of an undirected graph form a binary clutter, and that it is Mengerian is the max-flow min-cut theorem of Ford and Fulkerson; the theorem identifies exactly which binary clutters share this property. Its matroid form (the Corollary on p. 220) states that for a matroid $M$, the port $\Omega(M)$ is Mengerian for every element $\Omega$ if and only if $M$ is binary and has no $F_7^*$ minor.
--
--   **Formalization Note** Binary is taken in the form (3.2)(ii), which the paper quotes as equivalent to "port of a binary matroid" for every clutter. Weights and packings are $\mathbb N$-valued. "Has a $Q_6$ minor" means some minor is the image of $Q_6$ under an injective relabelling `Fin 6 ↪ α`.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 209, Theorem

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_IsClutter
import Definitions.Def_SeymourMFMC_Binary_IsBinary
import Definitions.Def_SeymourMFMC_Binary_IsMengerian
import Definitions.Def_SeymourMFMC_Binary_HasQ6Minor

namespace SeymourMFMC.Binary

/-- Seymour 1977, Theorem, p. 209: a binary clutter is Mengerian if and only if it has no `Q₆`
minor. -/
theorem theorem_mengerian_iff_no_Q6_minor {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : IsClutter L) (hbin : IsBinary L) :
    IsMengerian L ↔ ¬ HasQ6Minor L := by sorry

end SeymourMFMC.Binary
