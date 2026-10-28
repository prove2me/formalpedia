-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_ZT_marked_exclusion_card_bound
-- name    : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.marked_exclusion_card_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:45:17.483866+00:00
-- url     : https://prove2.me/theorems/6c3104b2-f5eb-464a-baaf-8f52775eccb4
-- title:
--   A marked-event exclusion bounds every admissible candidate set
-- statement:
--   Let \(T\) be a binary-labeled tournament, and fix natural numbers \(q,a,m,B\). Suppose every marked event with \(m\) markers, \(a\) candidate vertices, tolerance \(q\), and total mismatch budget \(B\) is absent. Then any disjoint candidate and marker sets \(A,M\), with \(|M|=m\), no distinguished positive markers, and the marked-coherence conditions at that budget satisfy
--   \[
--   |A|<a.
--   \]
--   This converts the indexed event exclusion into the cardinality bound used by actual repair configurations.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ArchivedExclusionBridge.lean, lines 76–95.

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

theorem Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.marked_exclusion_card_bound :
∀ {k : Nat} (T : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
  (label : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (q a m B : Nat)
  (h :
    ∀
      (I :
        @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.MarkedIndex.{0} (Fin k) (Fin.fintype k)
          (instDecidableEqFin k) a m),
      Not
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.SupportedFamily.bad.{0, 0} (Prod.{0, 0} (Fin k) (Fin k))
          (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.MarkedIndex.{0} (Fin k) (Fin.fintype k)
            (instDecidableEqFin k) a m)
          (fun (a b : Prod.{0, 0} (Fin k) (Fin k)) =>
            @instDecidableEqProd.{0, 0} (Fin k) (Fin k) (instDecidableEqFin k) (instDecidableEqFin k) a b)
          (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.markedFamily.{0} (Fin k) (Fin.fintype k)
            (instDecidableEqFin k)
            (@Digraph.Adj.{0} (Fin k)
              (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.toDigraph k T))
            q a m B)
          I fun (e : Prod.{0, 0} (Fin k) (Fin k)) =>
          label (@Prod.fst.{0, 0} (Fin k) (Fin k) e) (@Prod.snd.{0, 0} (Fin k) (Fin k) e))),
  @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.MarkedCardBound k T label q m
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) B a := by sorry
