-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_Sensitivity2075_tolerant_target_weak_false
-- name    : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerant_target_weak_false
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:54:31.442247+00:00
-- url     : https://prove2.me/theorems/bac0f915-af22-45cc-ad87-017a8ce0eb7c
-- title:
--   A strong target candidate remains false at its weak target witness
-- statement:
--   Let \(F\) be a nested Boolean family. Consider weak and strong tolerant rows with ordered target and guard levels, and tolerances \(q_j\le q_i\); assume there is at least one child color. If the weak parent is false and \(i\) is a target candidate for the strong parent, then the strong candidate's unique missing child also fails the weak target test:
--   \[
--   F_{A_i}(x_{i,\operatorname{missingWitness}(F_{A_j},x,i)})=\mathrm{false}.
--   \]
--   This supplies the weak-false condition required for a conditional upward-sensitivity charge.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ArchivedOrdinaryPositive.lean, lines 164–183.

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

theorem Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerant_target_weak_false :
∀ {n k r : Nat} {I : Type} (T : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.NestedFamily n I F) (Ai Aj Gi Gj : Fin n)
  (hA : @LE.le.{0} (Fin n) (@instLEFin n) Ai Aj) (hG : @LE.le.{0} (Fin n) (@instLEFin n) Gj Gi)
  (x : Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin r)) I → Bool) {qi qj : Nat} (hq : @LE.le.{0} Nat instLENat qj qi)
  (hr : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r)
  (hx :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily n k r I T label F Ai Gi qi x)
      Bool.false)
  {i : Fin k}
  (hi :
    @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
      (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k)))
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantTargets n k r I T label F Aj Gj qj x)
      i),
  @Eq.{1} Bool
    (F Ai
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.recursiveChild k r I x i
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.missingWitness n k r I F Aj x hr i)))
    Bool.false := by sorry
