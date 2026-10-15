-- Prove2me | Theorems.Thm_ThreeSum_LightSharedReportingLoop_forSum
-- name    : ThreeSum.LightSharedReportingLoop.forSum
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:35:20.776973+00:00
-- url     : https://prove2.me/theorems/29370c96-a8e1-4134-9637-a4229d0cce8e
-- title:
--   A counting-loop rule with summed iteration budgets
-- statement:
--   Fix a program, resource limits, and a call depth. Let a counting loop use counter register $i$, upper-bound expression $e$, body, and invariant predicates $I_j$, with $n\in\mathbb N$ iterations and individual body budgets $b_j\in\mathbb N$. Assume initialization establishes $I_0$; a body execution at counter $j<n$ costs at most $b_j$, preserves the counter, and establishes $I_{j+1}$ after incrementing it; and the terminal invariant implies $Q$. Assume $e$ is safe and equals $n$ at every invariant state through $j=n$, and $n$ fits in a word. If
--
--   $$\sum_{j=0}^{n-1}\bigl(\operatorname{cost}(e)+b_j+7\bigr)+\operatorname{cost}(e)+5\le T,$$
--
--   the loop terminates within $T$ steps with $Q$. This preserves per-iteration cost information in traversal budgets.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSharedReportingLoop.lean#L9-L65

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_Light_Ends_while


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightSharedReportingLoop.forSum : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {σ : Light.State} {i : Nat} {hi : Light.Expr} {body : Light.Stmt}
  {T : Nat} {Q : Light.State → Prop} (I : Nat → Light.State → Prop) (n : Nat) (b : Nat → Nat)
  (start :
    I (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      {
        loc :=
          @Function.update.{1, 1} Nat (fun (a : Nat) => Int) instDecidableEqNat σ.loc i
            (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))),
        mem := σ.mem })
  (round :
    ∀ (j : Nat) (σ : Light.State),
      @LT.lt.{0} Nat instLTNat j n →
        @Eq.{1} Int (σ.loc i) (@Nat.cast.{0} Int instNatCastInt j) →
          I j σ →
            Light.Ends lim P d body σ (b j) fun (σ' : Light.State) =>
              And (@Eq.{1} Int (σ'.loc i) (@Nat.cast.{0} Int instNatCastInt j))
                (I
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  {
                    loc :=
                      @Function.update.{1, 1} Nat (fun (a : Nat) => Int) instDecidableEqNat σ'.loc i
                        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                          (@Nat.cast.{0} Int instNatCastInt j)
                          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))),
                    mem := σ'.mem }))
  (done : ∀ (σ : Light.State), @Eq.{1} Int (σ.loc i) (@Nat.cast.{0} Int instNatCastInt n) → I n σ → Q σ)
  (bound :
    ∀ (j : Nat) (σ : Light.State),
      @LE.le.{0} Nat instLENat j n →
        @Eq.{1} Int (σ.loc i) (@Nat.cast.{0} Int instNatCastInt j) →
          I j σ →
            And (Light.Expr.Safe lim σ hi) (@Eq.{1} Int (Light.Expr.val σ hi) (@Nat.cast.{0} Int instNatCastInt n)))
  (hn : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt n) lim.word)
  (hT :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (∑ j ∈ Finset.range n,
            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hi.cost (b j))
              (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
          hi.cost)
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
      T),
  Light.Ends lim P d (Light.Stmt.for i hi body) σ T Q := by
  sorry
