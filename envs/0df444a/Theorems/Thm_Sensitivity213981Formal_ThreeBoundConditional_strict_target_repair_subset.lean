-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_strict_target_repair_subset
-- name    : Sensitivity213981Formal.ThreeBoundConditional.strict_target_repair_subset
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T19:43:53.48385+00:00
-- url     : https://prove2.me/theorems/a1995303-2a09-4006-9388-7999836c0fd7
-- title:
--   All strict repairs of a target candidate use its missing child
-- statement:
--   Suppose a row has no failed guards, exactly one designated target child is false at level t, and its other target child is true. Every single flip making the zero-tolerance row at target t and guard g accept lies in the lifted upward-sensitivity set at level t of that designated missing child.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; StrictUnion.lean, lines 226–252.

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictUnion
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

theorem Sensitivity213981Formal.ThreeBoundConditional.strict_target_repair_subset :
∀ {L I V : Type} [LinearOrder.{0} L] [inst : Fintype.{0} I] [inst_1 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool) (t g : L)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V) (c₀ : Bool)
  (hfalse : @Eq.{1} Bool (F t (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c₀)) Bool.false)
  (hother :
    ∀ (c : Bool),
      @Ne.{1} Bool c c₀ → @Eq.{1} Bool (F t (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)) Bool.true)
  (hg :
    @Eq.{1} (Finset.{0} V) (@Sensitivity213981Formal.ThreeBoundConditional.guardFailures L I V inst_1 S F g x v)
      (@EmptyCollection.emptyCollection.{0} (Finset.{0} V) (@Finset.instEmptyCollection.{0} V))),
  @LE.le.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
    (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@Finset.instPartialOrder.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))))
    (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_1 Bool.fintype) inst)
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryRowBool L I V inst_1 S F t g
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) v)
      Bool.true x)
    (@Sensitivity213981Formal.ThreeBoundPositive.liftBits I V v c₀
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst (F t) Bool.true
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c₀))) := by sorry
