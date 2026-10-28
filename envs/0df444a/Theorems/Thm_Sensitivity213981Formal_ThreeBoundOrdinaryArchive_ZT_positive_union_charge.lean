-- Prove2me | Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_ZT_positive_union_charge
-- name    : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.positive_union_charge
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-26T18:55:45.467772+00:00
-- url     : https://prove2.me/theorems/0b68e895-f247-4e17-ab20-4970a8d81bdb
-- title:
--   A two-cost union bound with positive-head savings
-- statement:
--   Let \(Z\) index finite sets \(D_v\), and classify its elements as inside or outside, and costly or cheap. Let \(E,W,L,u,\delta,s,j\) be natural numbers with \(j\le s\). Suppose \(|Z|\le E\), at most \(W\) indices are outside, \(W+L\le E\), at most \(2u\) are inside, at most \(u\) are both inside and costly, and at least \(\delta\) are outside and cheap. Assume \(|D_v|\le s\) for costly indices and \(|D_v|\le j\) otherwise. Then
--   \[
--   \left|\bigcup_{v\in Z}D_v\right|
--   \le \bigl(E-(L-u)-\delta\bigr)s+
--   \bigl(\min(u,L-u)+\delta\bigr)j.
--   \]
--   All subtractions are natural-number subtractions, truncated at zero. The result captures savings when several guard arcs share positive heads.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; ArchivedOrdinaryPositive.lean, lines 815–869.

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

theorem Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.positive_union_charge :
∀ {V α : Type} [DecidableEq.{1} V] [inst : DecidableEq.{1} α] (Z : Finset.{0} V) (inside costly : V → Prop)
  [inst_1 : @DecidablePred.{1} V inside] [inst_2 : @DecidablePred.{1} V costly] (D : V → Finset.{0} α)
  (E W L u δ s j : Nat) (hjs : @LE.le.{0} Nat instLENat j s) (hZ : @LE.le.{0} Nat instLENat (@Finset.card.{0} V Z) E)
  (hW :
    @LE.le.{0} Nat instLENat
      (@Finset.card.{0} V
        (@Finset.filter.{0} V (fun (v : V) => Not (inside v)) (fun (a : V) => @instDecidableNot (inside a) (inst_1 a))
          Z))
      W)
  (hL : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W L) E)
  (hin :
    @LE.le.{0} Nat instLENat (@Finset.card.{0} V (@Finset.filter.{0} V inside inst_1 Z))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) u))
  (hcost :
    @LE.le.{0} Nat instLENat
      (@Finset.card.{0} V
        (@Finset.filter.{0} V (fun (v : V) => And (inside v) (costly v))
          (fun (a : V) => @instDecidableAnd (inside a) (costly a) (inst_1 a) (inst_2 a)) Z))
      u)
  (hcheap :
    @LE.le.{0} Nat instLENat δ
      (@Finset.card.{0} V
        (@Finset.filter.{0} V (fun (v : V) => And (Not (inside v)) (Not (costly v)))
          (fun (a : V) =>
            @instDecidableAnd (Not (inside a)) (Not (costly a)) (@instDecidableNot (inside a) (inst_1 a))
              (@instDecidableNot (costly a) (inst_2 a)))
          Z)))
  (hD :
    ∀ (v : V),
      @Membership.mem.{0, 0} V (Finset.{0} V)
          (@SetLike.instMembership.{0, 0} (Finset.{0} V) V (@Finset.instSetLike.{0} V)) Z v →
        @LE.le.{0} Nat instLENat (@Finset.card.{0} α (D v)) (@ite.{1} Nat (costly v) (inst_2 v) s j)),
  @LE.le.{0} Nat instLENat (@Finset.card.{0} α (@Finset.biUnion.{0, 0} V α inst Z D))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) E
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L u))
          δ)
        s)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@Min.min.{0} Nat instMinNat u (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) L u)) δ)
        j)) := by sorry
