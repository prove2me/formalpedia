-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundConditionalNumeric_parent_eq_ordinary_valid
-- name    : Sensitivity213981Formal.ThreeBoundConditionalNumeric.parent_eq_ordinary_valid
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T20:05:08.704098+00:00
-- url     : https://prove2.me/theorems/3ca5b70d-5568-4a20-9aca-beb49c0b9e8d
-- title:
--   A constant target on feasible counts makes a stage parent ordinary
-- statement:
--   Fix a stage level l, a target level t and a finite child family F. Suppose that for every d≤S.tolerance(l) and all child inputs u,z, the stage target S.target(l,d,u,z) is F(t,u)∧F(t,z). Then the stage parent at l equals the ordinary parent with target t, guard S.guard(l) and tolerance S.tolerance(l). No condition on target values at infeasible counts is required.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RawConditionalBase.lean, lines 47–70.

import Definitions.Def_Sensitivity213981Formal_ConditionalOrdinary
import Definitions.Def_Sensitivity213981Formal_HeadCostExpressions
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_OrdinaryParentBridge
import Definitions.Def_Sensitivity213981Formal_WitnessLifting
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
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
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

theorem Sensitivity213981Formal.ThreeBoundConditionalNumeric.parent_eq_ordinary_valid :
∀ {n : Nat} {I V : Type} [Fintype.{0} I] [inst : Fintype.{0} V]
  (S : Sensitivity213981Formal.ThreeBoundWitness.Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (l t : Fin n)
  (hconstant :
    ∀ (d : Nat),
      @LE.le.{0} Nat instLENat d (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance (Fin n) I V S l) →
        ∀ (u z : I → Bool),
          @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundWitness.Stage.target (Fin n) I V S l d u z)
            (Bool.and (F t u) (F t z))),
  @Eq.{1} ((x : Prod.{0, 0} (Prod.{0, 0} V Bool) I → Bool) → Bool)
    (@Sensitivity213981Formal.ThreeBoundWitness.parent (Fin n) I V inst S F l)
    (@Sensitivity213981Formal.ThreeBoundConditional.ordinaryParent (Fin n) I V inst S F t
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.guard (Fin n) I V S l)
      (@Sensitivity213981Formal.ThreeBoundWitness.Stage.tolerance (Fin n) I V S l)) := by sorry
