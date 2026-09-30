-- Prove2me | Theorems.Thm_SeymourMFMC_Binary_parity_decomposition
-- name    : SeymourMFMC.Binary.parity_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T04:27:34.275089+00:00
-- url     : https://prove2.me/theorems/e0140ddc-741f-496c-b5f1-d7c6a36968df
-- title:
--   (3.6)(iii) — sets of even/odd blocker parity are disjoint unions of circuits (plus one member)
-- statement:
--   Let $\mathbf L$ be a binary clutter and $Z \subseteq E(\mathbf L)$.
--
--   1. If $|Z \cap B|$ is even for each $B \in b(\mathbf L)$, then $Z$ is a disjoint union of circuits of $\mathbf L$.
--   2. If $|Z \cap B|$ is odd for each $B \in b(\mathbf L)$, then $Z$ is a disjoint union of circuits of $\mathbf L$ together with one member of $\mathbf L$:
--   $$
--   Z = A \cup C_1 \cup \dots \cup C_k, \qquad A \in \mathbf L,
--   $$
--   with $A, C_1, \dots, C_k$ pairwise disjoint and each $C_i$ a circuit.
--
--   This parity principle is the main tool for producing circuits in Sections 4 and 5, typically from symmetric differences of members of $\mathbf L$.
--
--   **Formalization Note** The disjoint union is a finite family $\mathcal C$ of circuits, pairwise disjoint, with union $Z$ (in (b), each disjoint from $A$, and $A \cup \bigcup \mathcal C = Z$); $\mathcal C$ may be empty. The page's "In particular" sentence on symmetric differences follows from (a) and (b) and is not stated separately.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 202, (3.6)(iii)

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_ground
import Definitions.Def_SeymourMFMC_Binary_blocker
import Definitions.Def_SeymourMFMC_Binary_IsClutter
import Definitions.Def_SeymourMFMC_Binary_IsBinary
import Definitions.Def_SeymourMFMC_Binary_IsCircuit

namespace SeymourMFMC.Binary

/-- Seymour 1977, (3.6)(iii), p. 202: let `L` be a binary clutter and `Z ⊆ E(L)`.
(a) If `|Z ∩ B|` is even for each `B ∈ b(L)`, then `Z` is a disjoint union of circuits of `L`.
(b) If `|Z ∩ B|` is odd for each `B ∈ b(L)`, then `Z` is a disjoint union of circuits of `L`
together with one member of `L`. -/
theorem parity_decomposition {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : IsClutter L) (hbin : IsBinary L) (Z : Finset α) (hZ : Z ⊆ ground L) :
    ((∀ B ∈ blocker L, Even (Z ∩ B).card) →
      ∃ Cs : Finset (Finset α), (∀ C ∈ Cs, IsCircuit L C) ∧
        (Cs : Set (Finset α)).PairwiseDisjoint id ∧ Cs.sup id = Z) ∧
    ((∀ B ∈ blocker L, Odd (Z ∩ B).card) →
      ∃ A ∈ L, ∃ Cs : Finset (Finset α), (∀ C ∈ Cs, IsCircuit L C) ∧
        (Cs : Set (Finset α)).PairwiseDisjoint id ∧ (∀ C ∈ Cs, Disjoint C A) ∧
        A ∪ Cs.sup id = Z) := by sorry

end SeymourMFMC.Binary
