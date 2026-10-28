-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_SensitivityOrdinaryGuard_tournament_outside_budget
-- name    : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.SensitivityOrdinaryGuard.tournament_outside_budget
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:53:37.868776+00:00
-- url     : https://prove2.me/theorems/caad9c95-3b50-4424-9507-198761436967
-- title:
--   Internal tournament edges and external guard charges share one budget
-- statement:
--   Let \(P,R\) be disjoint vertex sets in a tournament. For each vertex \(i\), let \(B_i\) be a budget set containing every outgoing neighbor of \(i\) in \(P\cup R\). Assume \(|B_i|\le q\) for \(i\in P\) and \(|B_i|=q+1\) for \(i\in R\). Let \(O_i\subseteq B_i\) avoid \(R\). Then
--   \[
--   \sum_{i\in R}|O_i\setminus P|+\binom{|P|+|R|}{2}
--   \le q|P|+(q+1)|R|.
--   \]
--   The inequality prevents external repair charges from being counted independently of the internal edges that already consume the same budgets.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ArchivedOrdinaryPositive.lean, lines 896–950.

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

theorem Sensitivity213981Formal.ThreeBoundOrdinaryArchive.SensitivityOrdinaryGuard.tournament_outside_budget :
∀ {k : Nat} (T : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k) (P R : Finset.{0} (Fin k))
  (B O : Fin k → Finset.{0} (Fin k)) (q : Nat)
  (hdis :
    @Disjoint.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k)) (@Finset.instOrderBot.{0} (Fin k)) P R)
  (hinside :
    ∀ (i : Fin k),
      @LE.le.{0} (Finset.{0} (Fin k))
        (@Preorder.toLE.{0} (Finset.{0} (Fin k))
          (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k))))
        (@Finset.filter.{0} (Fin k)
          (@Digraph.Adj.{0} (Fin k)
            (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.toDigraph k T) i)
          (fun (a : Fin k) =>
            Classical.propDecidable
              (@Digraph.Adj.{0} (Fin k)
                (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.toDigraph k T) i a))
          (@Union.union.{0} (Finset.{0} (Fin k)) (@Finset.instUnion.{0} (Fin k) (instDecidableEqFin k)) P R))
        (B i))
  (hP :
    ∀ (i : Fin k),
      @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
          (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) P i →
        @LE.le.{0} Nat instLENat (@Finset.card.{0} (Fin k) (B i)) q)
  (hR :
    ∀ (i : Fin k),
      @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
          (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) R i →
        @Eq.{1} Nat (@Finset.card.{0} (Fin k) (B i))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (hOB :
    ∀ (i : Fin k),
      @LE.le.{0} (Finset.{0} (Fin k))
        (@Preorder.toLE.{0} (Finset.{0} (Fin k))
          (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k))))
        (O i) (B i))
  (hOR :
    ∀ (i j : Fin k),
      @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
          (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) (O i) j →
        Not
          (@Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
            (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) R j)),
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@Finset.sum.{0, 0} (Fin k) Nat Nat.instAddCommMonoid R fun (i : Fin k) =>
        @Finset.card.{0} (Fin k)
          (@Finset.filter.{0} (Fin k)
            (fun (j : Fin k) =>
              Not
                (@Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) P j))
            (fun (a : Fin k) =>
              @instDecidableNot
                (@Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) P a)
                (@Finset.decidableMem.{0} (Fin k) (instDecidableEqFin k) a P))
            (O i)))
      (Nat.choose
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Finset.card.{0} (Fin k) P)
          (@Finset.card.{0} (Fin k) R))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q (@Finset.card.{0} (Fin k) P))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Finset.card.{0} (Fin k) R))) := by sorry
