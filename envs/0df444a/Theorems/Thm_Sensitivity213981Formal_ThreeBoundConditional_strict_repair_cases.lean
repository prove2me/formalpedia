-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_strict_repair_cases
-- name    : Sensitivity213981Formal.ThreeBoundConditional.strict_repair_cases
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T19:38:53.429772+00:00
-- url     : https://prove2.me/theorems/7df1ea58-9fae-4126-a40c-c0b5d6b90e59
-- title:
--   A zero-tolerance row is repaired at its sole target or sole guard defect
-- statement:
--   Suppose a zero-tolerance ordinary row \(v\) is false before a single flip and true afterwards. Then either the flip is in its own child, that child is the unique failed target, and the old guard-failure set is empty; or both old targets are true and the old guard-failure set is exactly \(\{w\}\), where the flipped child is selected by the edge \(v\to w\). In the second case the selected guard changes from true to false. This precisely classifies the strict-row repair positions.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; StrictUnion.lean, lines 85–165.

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictUnion
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundConditional.strict_repair_cases :
∀ {L I V : Type} [LinearOrder.{0} L] [Fintype.{0} I] [inst : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool) (t g : L)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v w : V) (c : Bool) (a : I)
  (hoff :
    Not
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryRow L I V inst S F t g
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) x v))
  (hon :
    @Sensitivity213981Formal.ThreeBoundConditional.ordinaryRow L I V inst S F t g
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@OAI.Paper320.flip (Prod.{0, 0} (Prod.{0, 0} V Bool) I) x
        (@Singleton.singleton.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Finset.instSingleton.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Prod.mk.{0, 0} (Prod.{0, 0} V Bool) I (@Prod.mk.{0, 0} V Bool w c) a)))
      v),
  Or
    (And (@Eq.{1} V w v)
      (And (@Eq.{1} Bool (F t (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)) Bool.false)
        (And
          (∀ (e : Bool),
            @Ne.{1} Bool e c →
              @Eq.{1} Bool (F t (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v e)) Bool.true)
          (And
            (@Eq.{1} (Finset.{0} V) (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst S F g x v)
              (@EmptyCollection.emptyCollection.{0} (Finset.{0} V) (@Finset.instEmptyCollection.{0} V)))
            (@Eq.{1} Bool
              (F t
                (@OAI.Paper320.flip I (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)
                  (@Singleton.singleton.{0, 0} I (Finset.{0} I) (@Finset.instSingleton.{0} I) a)))
              Bool.true)))))
    (And (∀ (e : Bool), @Eq.{1} Bool (F t (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v e)) Bool.true)
      (And
        (@Eq.{1} (Finset.{0} V) (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst S F g x v)
          (@Singleton.singleton.{0, 0} V (Finset.{0} V) (@Finset.instSingleton.{0} V) w))
        (And (@Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S v w)
          (And (@Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w) c)
            (And (@Eq.{1} Bool (F g (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w c)) Bool.true)
              (@Eq.{1} Bool
                (F g
                  (@OAI.Paper320.flip I (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w c)
                    (@Singleton.singleton.{0, 0} I (Finset.{0} I) (@Finset.instSingleton.{0} I) a)))
                Bool.false)))))) := by sorry
