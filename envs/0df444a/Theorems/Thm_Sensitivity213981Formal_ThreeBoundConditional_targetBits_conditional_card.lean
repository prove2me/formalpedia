-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_targetBits_conditional_card
-- name    : Sensitivity213981Formal.ThreeBoundConditional.targetBits_conditional_card
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T19:32:31.732748+00:00
-- url     : https://prove2.me/theorems/772aa418-c77a-470f-956c-cd49e803e003
-- title:
--   Two target children have a refined conditional downward cost
-- statement:
--   Consider two children that are both true at level \(t_j\), with at least one false at level \(t_k\). If \(M_F(t_i,t_j,t_k)\le m\) and \(B_F(t_i,t_k)\le b\), then
--   \[
--   |\operatorname{targetBits}(F,t_i,x,v)|\le\max(2m,m+b).
--   \]
--   This improves the unconditional sum of two downward bounds when a later target is known to fail.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ConditionalOrdinary.lean, lines 117–137.

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundConditional.targetBits_conditional_card :
∀ {L I V : Type} [LinearOrder.{0} L] [inst : Fintype.{0} I] [Fintype.{0} V] (F : L → (I → Bool) → Bool) (ti tj tk : L)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V) (m b : Nat)
  (hm : @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst F ti tj tk m)
  (hb : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst F ti tk b)
  (ht : ∀ (c : Bool), @Eq.{1} Bool (F tj (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)) Bool.true)
  (hmiss :
    @Exists.{1} Bool fun (c : Bool) =>
      @Eq.{1} Bool (F tk (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)) Bool.false),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Sensitivity213981Formal.ThreeBoundPositive.targetBits L I V inst F ti x v))
    (@Max.max.{0} Nat Nat.instMax
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m b)) := by sorry
