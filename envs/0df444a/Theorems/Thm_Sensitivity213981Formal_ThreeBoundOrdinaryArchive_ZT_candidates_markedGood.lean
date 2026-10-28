-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_ZT_candidates_markedGood
-- name    : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.candidates_markedGood
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:43:25.64636+00:00
-- url     : https://prove2.me/theorems/101e5ef8-fb7f-4e48-8700-e42884d8e25d
-- title:
--   Target and guard candidates satisfy the marked-coherence conditions
-- statement:
--   Let \(T\) be a binary-labeled tournament and \(F\) a nested Boolean family, with guard level \(g\le t\) and tolerance \(q\). Let \(A\) be a set of target candidates, let \(M\) consist of positive target candidates or guard candidates, and let \(P\) be a set of positive target candidates. Assume \(A\cap M=\varnothing\). Color each vertex by its missing target witness. If the sum of outgoing mismatches from markers into \(A\) is at most \(B\), then
--   \[
--   \operatorname{MarkedGood}(A,M,P,q,B)
--   \]
--   holds. This realizes an abstract marked obstruction using actual Boolean repair candidates.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ArchivedOrdinaryCaps.lean, lines 659–687.

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_Supplement_ArchivedOrdinaryDefinitions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.candidates_markedGood :
∀ {n k : Nat} {I : Type} (T : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
  (label : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (F : Fin n → (I → Bool) → Bool)
  (hF : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.NestedFamily n I F) (t g : Fin n)
  (hgt : @LE.le.{0} (Fin n) (@instLEFin n) g t) (q B : Nat)
  (x : Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I → Bool)
  (A M P : Finset.{0} (Fin k))
  (hA :
    @LE.le.{0} (Finset.{0} (Fin k))
      (@Preorder.toLE.{0} (Finset.{0} (Fin k))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k))))
      A
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantTargets n k
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F t g q x))
  (hM :
    @LE.le.{0} (Finset.{0} (Fin k))
      (@Preorder.toLE.{0} (Finset.{0} (Fin k))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k))))
      M
      (@Union.union.{0} (Finset.{0} (Fin k)) (@Finset.instUnion.{0} (Fin k) (instDecidableEqFin k))
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.SensitivityQ.positiveTargets n k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F t g q x
          (@of_decide_eq_true
            (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@id.{0}
              (@Eq.{1} Bool
                (@Decidable.decide
                  (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                Bool.true)
              (@Eq.refl.{1} Bool Bool.true))))
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantGuards n k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F t g q x)))
  (hP :
    @LE.le.{0} (Finset.{0} (Fin k))
      (@Preorder.toLE.{0} (Finset.{0} (Fin k))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k))))
      P
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.SensitivityQ.positiveTargets n k
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F t g q x
        (@of_decide_eq_true
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@id.{0}
            (@Eq.{1} Bool
              (@Decidable.decide
                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              Bool.true)
            (@Eq.refl.{1} Bool Bool.true)))))
  (hdis :
    @Disjoint.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k)) (@Finset.instOrderBot.{0} (Fin k)) A M)
  (hB :
    @LE.le.{0} Nat instLENat
      (@Finset.sum.{0, 0} (Fin k) Nat Nat.instAddCommMonoid M fun (y : Fin k) =>
        @Finset.card.{0} (Fin k)
          (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.mismatch.{0} (Fin k)
            (@Digraph.Adj.{0} (Fin k)
              (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.toDigraph k T))
            (fun (e : Prod.{0, 0} (Fin k) (Fin k)) =>
              label (@Prod.fst.{0, 0} (Fin k) (Fin k) e) (@Prod.snd.{0, 0} (Fin k) (Fin k) e))
            A
            (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.missingWitness n k
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I F t x
              (@of_decide_eq_true
                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@id.{0}
                  (@Eq.{1} Bool
                    (@Decidable.decide
                      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    Bool.true)
                  (@Eq.refl.{1} Bool Bool.true))))
            y))
      B),
  @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.MarkedGood.{0} (Fin k) (instDecidableEqFin k)
    (@Digraph.Adj.{0} (Fin k)
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.toDigraph k T))
    (fun (e : Prod.{0, 0} (Fin k) (Fin k)) =>
      label (@Prod.fst.{0, 0} (Fin k) (Fin k) e) (@Prod.snd.{0, 0} (Fin k) (Fin k) e))
    A M P q B
    (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.missingWitness n k
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I F t x
      (@of_decide_eq_true
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@id.{0}
          (@Eq.{1} Bool
            (@Decidable.decide
              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            Bool.true)
          (@Eq.refl.{1} Bool Bool.true)))) := by sorry
