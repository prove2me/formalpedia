-- Prove2me | Theorems.Thm_Sensitivity213981Formal_GuardAugmentation_exists_near_coloring
-- name    : Sensitivity213981Formal.GuardAugmentation.exists_near_coloring
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:27:26.568709+00:00
-- url     : https://prove2.me/theorems/4bd663ab-cf54-42f5-977c-2a86cc1905cf
-- title:
--   One binary coloring matches an outgoing edge at all but one vertex
-- statement:
--   Let \(V\) be finite, and let \(R\) be a relation such that every pair of distinct vertices is related in at least one direction. For any Boolean edge labeling \(\ell\), there are a vertex coloring \(c\) and a set \(B\subseteq V\) with
--   \[
--   |B|\le1,\qquad
--   \forall x\notin B,\ \exists y:\ R(x,y)\ \text{and}\ \ell(x,y)=c(y).
--   \]
--   The statement also includes the empty vertex type. This coloring is used to absorb guard vertices while losing at most one vertex.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; GuardAugmentation.lean, lines 76–97.

import Definitions.Def_Sensitivity213981Formal_GuardAugmentation
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.GuardAugmentation.exists_near_coloring :
∀ {V : Type} [Fintype.{0} V] [DecidableEq.{1} V] (R : V → V → Prop)
  (ht : ∀ (x y : V), @Ne.{1} V x y → Or (R x y) (R y x)) (label : V → V → Bool),
  @Exists.{1} (V → Bool) fun (color : V → Bool) =>
    @Exists.{1} (Finset.{0} V) fun (bad : Finset.{0} V) =>
      And
        (@LE.le.{0} Nat instLENat (@Finset.card.{0} V bad)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (∀ (x : V),
          Not
              (@Membership.mem.{0, 0} V (Finset.{0} V)
                (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) bad x) →
            @Exists.{1} V fun (y : V) => And (R x y) (@Eq.{1} Bool (label x y) (color y))) := by sorry
