-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundPositive_failed_after_subset_of_no_extra
-- name    : Sensitivity213981Formal.ThreeBoundPositive.failed_after_subset_of_no_extra
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:26:25.347498+00:00
-- url     : https://prove2.me/theorems/b26553ed-302f-474d-ac2d-e3f500149de5
-- title:
--   Without a new failure, the old strong guard set covers the new weak one
-- statement:
--   Let \(F\) be nested, and let stage levels \(i,j\) satisfy \(\operatorname{guard}(j)\le\operatorname{guard}(i)\). Fix a row and a single child-bit flip. If that flip creates no extra weak guard failure at a location that previously passed the strong guard test, then
--   \[
--   \operatorname{failed}_i(x^{\{a\}})\subseteq\operatorname{failed}_j(x).
--   \]
--   This inclusion controls changes in the guard count when bounding positive-boundary sensitivity.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; GradedPositiveBoundary.lean, lines 44–64.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
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

theorem Sensitivity213981Formal.ThreeBoundPositive.failed_after_subset_of_no_extra :
∀ {L I V : Type} [inst : Preorder.{0} L] [Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool)
  (hF : @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I inst F) (i j : L)
  (hg :
    @LE.le.{0} L (@Preorder.toLE.{0} L inst) (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S j)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard L I V S i))
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v w : V) (c : Bool) (a : I)
  (he : Not (@Sensitivity213981Formal.ThreeBoundPositive.ExtraFailure L I V S F i j x v w c a)),
  @LE.le.{0} (Finset.{0} V)
    (@Preorder.toLE.{0} (Finset.{0} V) (@PartialOrder.toPreorder.{0} (Finset.{0} V) (@Finset.instPartialOrder.{0} V)))
    (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_2 S F i
      (@OAI.Paper320.flip (Prod.{0, 0} (Prod.{0, 0} V Bool) I) x
        (@Singleton.singleton.{0, 0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Finset.instSingleton.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
          (@Prod.mk.{0, 0} (Prod.{0, 0} V Bool) I (@Prod.mk.{0, 0} V Bool w c) a)))
      v)
    (@Sensitivity213981Formal.ThreeBoundWitness.failed L I V inst_2 S F j x v) := by sorry
