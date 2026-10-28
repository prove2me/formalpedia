-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_same_row_up_guard_subset
-- name    : Sensitivity213981Formal.ThreeBoundConditional.same_row_up_guard_subset
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T19:40:33.258686+00:00
-- url     : https://prove2.me/theorems/ec34b5ce-a6d2-477c-ade6-602ea24a132f
-- title:
--   A known failed guard localizes every repair of a zero-tolerance row
-- statement:
--   For a row v, suppose an outgoing neighbor w₀ has its selected child true at guard level g_k, and let g_l≤g_k. Every single-bit flip that makes the zero-tolerance row with guard level g_l and any target level t_l accept must occur in that selected child and make its g_l value false.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; StrictPositive.lean, lines 205–223.

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictPositive
import Definitions.Def_Sensitivity213981Formal_StrictUnion
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundConditional.same_row_up_guard_subset :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [inst_1 : Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (gk tl gl : L)
  (hg :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      gl gk)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v w₀ : V)
  (hR : @Sensitivity213981Formal.ThreeBoundWitness.Stage.Adj L I V S v w₀)
  (hgk :
    @Eq.{1} Bool
      (F gk
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w₀
          (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w₀)))
      Bool.true),
  @LE.le.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
    (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
      (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@Finset.instPartialOrder.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))))
    (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
      (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryRowBool L I V inst_2 S F tl gl
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) v)
      Bool.true x)
    (@Sensitivity213981Formal.ThreeBoundPositive.liftBits I V w₀
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w₀)
      (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo I inst_1 (F gl) Bool.false
        (@Sensitivity213981Formal.ThreeBoundWitness.child I V x w₀
          (@Sensitivity213981Formal.ThreeBoundWitness.Stage.label L I V S v w₀)))) := by sorry
