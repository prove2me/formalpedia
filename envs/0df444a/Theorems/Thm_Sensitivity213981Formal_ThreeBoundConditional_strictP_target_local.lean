-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditional_strictP_target_local
-- name    : Sensitivity213981Formal.ThreeBoundConditional.strictP_target_local
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T19:39:33.476993+00:00
-- url     : https://prove2.me/theorems/5fcc6b26-d6ad-4d22-b2dc-cf3fbb0cd1c2
-- title:
--   Target destruction and same-row repairs share a conditional union bound
-- statement:
--   Suppose both target children of a row are true at t_j and at least one is false at t_k, with t_k≤t_l. Let M(g_l,t_j,t_k)≤m, B(g_l,t_k)≤b_k, B(g_l,t_l)≤b_l and D(g_l,t_j,t_k,t_l)≤u. The union of target-child destruction at g_l and flips making the zero-tolerance row at t_l,g_l accept has size at most max(max(2m,m+b_k),u+b_l).
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; StrictPositive.lean, lines 303–332.

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_StrictPositive
import Definitions.Def_Sensitivity213981Formal_StrictUnion
import Definitions.Def_Sensitivity213981Formal_Supplement_GradedPositiveBoundary
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

theorem Sensitivity213981Formal.ThreeBoundConditional.strictP_target_local :
∀ {L I V : Type} [inst : LinearOrder.{0} L] [inst_1 : Fintype.{0} I] [inst_2 : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage L I V) (F : L → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested L I
      (@PartialOrder.toPreorder.{0} L
        (@SemilatticeInf.toPartialOrder.{0} L
          (@Lattice.toSemilatticeInf.{0} L
            (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst)))))
      F)
  (tj tk tl gl : L)
  (ht :
    @LE.le.{0} L
      (@Preorder.toLE.{0} L
        (@PartialOrder.toPreorder.{0} L
          (@SemilatticeInf.toPartialOrder.{0} L
            (@Lattice.toSemilatticeInf.{0} L
              (@DistribLattice.toLattice.{0} L (@instDistribLatticeOfLinearOrder.{0} L inst))))))
      tk tl)
  (x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) (v : V)
  (htj : ∀ (c : Bool), @Eq.{1} Bool (F tj (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)) Bool.true)
  (hmiss :
    @Exists.{1} Bool fun (c : Bool) =>
      @Eq.{1} Bool (F tk (@Sensitivity213981Formal.ThreeBoundWitness.child I V x v c)) Bool.false)
  (m bₖ bₗ u : Nat) (hm : @Sensitivity213981Formal.ThreeBoundProfiles.MBound L I inst_1 F gl tj tk m)
  (hbₖ : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F gl tk bₖ)
  (hbₗ : @Sensitivity213981Formal.ThreeBoundProfiles.BBound L I inst_1 F gl tl bₗ)
  (hu : @Sensitivity213981Formal.ThreeBoundProfiles.DBound L I inst_1 F gl tj tk tl u),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
      (@Union.union.{0} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I))
        (@Finset.instUnion.{0} (Prod.{0, 0} (Prod.{0, 0} V Bool) I) fun (a b : Prod.{0, 0} (Prod.{0, 0} V Bool) I) =>
          @instDecidableEqProd.{0, 0} (Prod.{0, 0} V Bool) I
            (fun (a b : Prod.{0, 0} V Bool) =>
              @instDecidableEqProd.{0, 0} V Bool (fun (a b : V) => Classical.propDecidable (@Eq.{1} V a b))
                instDecidableEqBool a b)
            (fun (a b : I) => Classical.propDecidable (@Eq.{1} I a b)) a b)
        (@Sensitivity213981Formal.ThreeBoundPositive.targetBits L I V inst_1 F gl x v)
        (@Sensitivity213981Formal.ThreeBoundProfiles.flipsTo (Prod.{0, 0} (Prod.{0, 0} V Bool) I)
          (@instFintypeProd.{0, 0} (Prod.{0, 0} V Bool) I (@instFintypeProd.{0, 0} V Bool inst_2 Bool.fintype) inst_1)
          (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryRowBool L I V inst_2 S F tl gl
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) v)
          Bool.true x)))
    (@Max.max.{0} Nat Nat.instMax
      (@Max.max.{0} Nat Nat.instMax
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m bₖ))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) u bₗ)) := by sorry
