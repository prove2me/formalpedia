-- Prove2me | Theorems.Thm_Reduce_push_node_correct
-- name    : Reduce.push_node_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:13:08.111246+00:00
-- url     : https://prove2.me/theorems/43255d84-4ce8-4abb-a8c1-3ecb5d0faffe
-- title:
--   Reduce: push node correct
-- statement:
--   Pushing a fresh node for a non-ISO queue entry produces a correct, reduced BDD
--       that evaluates like the original sub-BDD at entry.2.  The common special case of
--       `push_node_correct'` where the whole heap lies above level `i` (`AllAbove`), so the
--       prefix is the entire heap and freshness follows from the variable ordering.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Process.lean#L482-L509
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Reduce/Process.lean#L482-L509

import Definitions.Def_Bdd_Reduce_Populate
import Definitions.Def_Bdd_Reduce_Process
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered RawBdd.RawPointer RawBdd.RawPointer.Bounded Subrelation
open Pointer
open Bdd
open RawBdd
open Reduce

theorem Reduce.push_node_correct {n m : Nat} {i : Nat}
    (O : OBdd n m)
    (ps : ProvedState n m)
    (inv : Invariant O ps i)
    (entry : (RawPointer × RawPointer) × Fin m)
    (hec : EntryCorrect O ps i entry)
    (hbound : entry.1.1.Bounded ps.state.size ∧ entry.1.2.Bounded ps.state.size)
    (hnonred : entry.1.1 ≠ entry.1.2)
    (hallabove : AllAbove ps i)
    (hheapinj : HeapInjective ps) :
    let hN  : (RawNode.mk O.1.heap[entry.2].var entry.1.1 entry.1.2).Bounded
                ps.state.size := ⟨hbound.1, hbound.2⟩
    let ps₁ := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).1
    let ptr := (push_node ps ⟨O.1.heap[entry.2].var, entry.1.1, entry.1.2⟩ hN).2
    let ps₂ := set_id ps₁ entry.2 ptr
    ∃ hj  : Bdd.Ordered ⟨O.1.heap, .node entry.2⟩,
    ∃ hp  : ptr.Bounded ps₂.state.size,
    ∃ ho  : Bdd.Ordered ⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩,
      OBdd.Reduced ⟨⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩, ho⟩ ∧
      ∀ I, OBdd.evaluate ⟨⟨cook_heap ps₂.state.heap ps₂.hh, ptr.cook hp⟩, ho⟩ I =
           OBdd.evaluate ⟨⟨O.1.heap, .node entry.2⟩, hj⟩ I := by sorry
