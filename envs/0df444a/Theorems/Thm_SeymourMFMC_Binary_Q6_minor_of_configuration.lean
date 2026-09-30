-- Prove2me | Theorems.Thm_SeymourMFMC_Binary_Q6_minor_of_configuration
-- name    : SeymourMFMC.Binary.Q6_minor_of_configuration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T05:09:49.446665+00:00
-- url     : https://prove2.me/theorems/0b5b1d3e-8d49-46f6-8cb0-72f9f2e00377
-- title:
--   (5.1) — a six-element circuit configuration forces a Q₆ minor
-- statement:
--   Let $\mathbf L$ be a binary clutter, and suppose there exist $Z \subseteq E(\mathbf L)$ and $A \in \mathbf L$ such that
--
--   1. $|Z| = 6$ and $Z = \{x_1, y_1, x_2, y_2, x_3, y_3\}$;
--   2. for $1 \le i < j \le 3$, $\{x_i, y_i, x_j, y_j\}$ is a circuit of $\mathbf L$;
--   3. $Z$ includes no other circuits of $\mathbf L$;
--   4. for $i = 1, 2, 3$, $A$ contains one but not both of $x_i, y_i$;
--   5. if $A' \in \mathbf L$ and $A' \subseteq A \cup Z$, then $A' - Z = A - Z$.
--
--   Then $\mathbf L$ has a $Q_6$ minor.
--
--   This is the device by which the minimal counterexample in Section 5 is shown to contain $Q_6$ (steps (5.35) and (5.37)).
--
--   **Formalization Note** The indices $1, 2, 3$ are `Fin 3`, the six elements are given by two maps $x, y$ from `Fin 3`, and $|Z| = 6$ makes them pairwise distinct.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 209, (5.1)

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_ground
import Definitions.Def_SeymourMFMC_Binary_IsClutter
import Definitions.Def_SeymourMFMC_Binary_IsBinary
import Definitions.Def_SeymourMFMC_Binary_IsCircuit
import Definitions.Def_SeymourMFMC_Binary_HasQ6Minor

namespace SeymourMFMC.Binary

/-- Seymour 1977, (5.1), p. 209: let `L` be a binary clutter, and suppose there exist
`Z ⊆ E(L)` and `A ∈ L` such that (i) `|Z| = 6` and `Z = {x₁, y₁, x₂, y₂, x₃, y₃}`;
(ii) `{xᵢ, yᵢ, xⱼ, yⱼ}` is a circuit of `L` for `1 ≤ i < j ≤ 3`; (iii) `Z` includes no other
circuits of `L`; (iv) for `i = 1, 2, 3`, `A` contains exactly one of `xᵢ, yᵢ`; (v) every
`A' ∈ L` with `A' ⊆ A ∪ Z` has `A' − Z = A − Z`. Then `L` has a `Q₆` minor. Indices `1, 2, 3`
are `Fin 3`. -/
theorem Q6_minor_of_configuration {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : IsClutter L) (hbin : IsBinary L) (x y : Fin 3 → α) (A : Finset α) (hA : A ∈ L)
    (hcard : (Finset.univ.image x ∪ Finset.univ.image y).card = 6)
    (hZ : Finset.univ.image x ∪ Finset.univ.image y ⊆ ground L)
    (hcirc : ∀ i j : Fin 3, i < j → IsCircuit L {x i, y i, x j, y j})
    (honly : ∀ C ⊆ Finset.univ.image x ∪ Finset.univ.image y, IsCircuit L C →
      ∃ i j : Fin 3, i < j ∧ C = {x i, y i, x j, y j})
    (hA_meets : ∀ i : Fin 3, (x i ∈ A ∧ y i ∉ A) ∨ (y i ∈ A ∧ x i ∉ A))
    (hA_min : ∀ A' ∈ L, A' ⊆ A ∪ (Finset.univ.image x ∪ Finset.univ.image y) →
      A' \ (Finset.univ.image x ∪ Finset.univ.image y) =
        A \ (Finset.univ.image x ∪ Finset.univ.image y)) :
    HasQ6Minor L := by sorry

end SeymourMFMC.Binary
