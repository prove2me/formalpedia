-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_ZL_markedGood_mono
-- name    : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.markedGood_mono
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:40:40.911461+00:00
-- url     : https://prove2.me/theorems/278c61a3-3801-4e0f-b053-850f0a737b6a
-- title:
--   Marked coherence persists under restriction and budget enlargement
-- statement:
--   Fix a directed relation \(R\), binary edge labels, a coloring, and a marker set \(M\). Let \(A'\subseteq A\), \(P'\subseteq P\), and \(B\le B'\). If \(A,M,P\) satisfy the marked-coherence conditions at tolerance \(q\) with total marker mismatch budget \(B\), then
--   \[
--   \operatorname{MarkedGood}(A',M,P',q,B')
--   \]
--   holds for the same relation, labels, and coloring. The conditions bound local mismatch counts and the sum of marker mismatches. This restriction principle allows a large configuration to be reduced to the fixed sizes of a forbidden event.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ArchivedOrdinaryCaps.lean, lines 51–78.

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

theorem Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.markedGood_mono.{u_1} :
∀ {V : Type u_1} [Fintype.{u_1} V] [inst : DecidableEq.{u_1 + 1} V] (R : V → V → Prop)
  (ell : Prod.{u_1, u_1} V V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (A A' M P P' : Finset.{u_1} V)
  (hA :
    @LE.le.{u_1} (Finset.{u_1} V)
      (@Preorder.toLE.{u_1} (Finset.{u_1} V)
        (@PartialOrder.toPreorder.{u_1} (Finset.{u_1} V) (@Finset.instPartialOrder.{u_1} V)))
      A' A)
  (hP :
    @LE.le.{u_1} (Finset.{u_1} V)
      (@Preorder.toLE.{u_1} (Finset.{u_1} V)
        (@PartialOrder.toPreorder.{u_1} (Finset.{u_1} V) (@Finset.instPartialOrder.{u_1} V)))
      P' P)
  (q B B' : Nat) (hB : @LE.le.{0} Nat instLENat B B')
  (color : V → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (hg : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.MarkedGood.{u_1} V inst R ell A M P q B color),
  @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZL.MarkedGood.{u_1} V inst R ell A' M P' q B' color := by sorry
