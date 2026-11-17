-- Prove2me | Theorems.Thm_QuantumLTF_Majority_card_symmDiff_add_twice_inter
-- name    : QuantumLTF.Majority.card_symmDiff_add_twice_inter
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-16T22:54:27.612192+00:00
-- url     : https://prove2.me/theorems/ecea50f3-25f5-40e3-be1d-9e82fd2c76af
-- title:
--   Cardinality decomposition for symmetric difference
-- statement:
--   For finite sets $A$ and $B$, their total cardinality with multiplicity decomposes into the symmetric difference and two copies of the intersection:
--
--   $$
--   |A\triangle B|+2|A\cap B|=|A|+|B|.
--   $$
--
--   In particular, $|A\triangle B|$ and $|A|+|B|$ have the same parity. This parity consequence is the finite-set step behind multiplication of Boolean Walsh characters.
-- source:
--   Elementary finite-set cardinality identity for symmetric difference.

import Mathlib

namespace QuantumLTF.Majority

open scoped symmDiff

theorem card_symmDiff_add_twice_inter : ∀ {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α), (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card := by sorry

end QuantumLTF.Majority
