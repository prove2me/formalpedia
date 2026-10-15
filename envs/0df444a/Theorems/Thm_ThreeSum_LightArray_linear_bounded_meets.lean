-- Prove2me | Theorems.Thm_ThreeSum_LightArray_linear_bounded_meets
-- name    : ThreeSum.LightArray.linear_bounded_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:33:02.386394+00:00
-- url     : https://prove2.me/theorems/68ca5a3b-e137-415e-8b89-a5890a6e7f95
-- title:
--   Bounded array addition and subtraction with safe in-place sources
-- statement:
--   Let a Light program contain the linear array body. For natural $n,U$, integer $c$ with $|c|\le1$, and source and destination addresses $A,B,D$, assume all length-$n$ intervals fit within $\mathrm{space}\le\mathrm{word}$. Each source must either start at $D$ or be disjoint from the destination. Suppose $2U\le\mathrm{word}$ and $|\mu(A+i)|,|\mu(B+i)|\le U$ for $i<n$.
--
--   The call with $(A,B,D,n,c)$ terminates within $23n+6$ steps and yields
--   $$
--   \nu(D+i)=\mu(A+i)+c\mu(B+i)\quad(i<n),
--   $$
--   while preserving memory outside $[D,D+n)$.
--
--   This supplies array addition, subtraction and copying with a uniform sufficient bound on intermediate values.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightArray.lean#L56-L78

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Light_Ends_pass


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightArray.linear_bounded_meets : ∀ {lim : Light.Limits} {P : Light.Program} {d p : Nat}
  (hp :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt ThreeSum.LightArray.linearBody))
  {μ : Nat → Int} {srcA srcB dst n U : Nat} {c : Int}
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hA : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcA n) lim.space)
  (hB : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB n) lim.space)
  (hD : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst n) lim.space)
  (hsepA : ThreeSum.LightArray.SourceSafe srcA dst n) (hsepB : ThreeSum.LightArray.SourceSafe srcB dst n)
  (hc :
    @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup c)
      (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) (@Nat.cast.{0} Int instNatCastInt U))
      lim.word)
  (hvalues :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        And
          (@LE.le.{0} Int Int.instLEInt
            (@abs.{0} Int instLatticeInt Int.instAddGroup
              (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcA i)))
            (@Nat.cast.{0} Int instNatCastInt U))
          (@LE.le.{0} Int Int.instLEInt
            (@abs.{0} Int instLatticeInt Int.instAddGroup
              (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB i)))
            (@Nat.cast.{0} Int instNatCastInt U))),
  Light.Meets lim P p d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcA)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcB)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n) (@List.cons.{0} Int c (@List.nil.{0} Int))))))
    μ (ThreeSum.LightArray.linearTime n) fun (x : Int) (μ' : Nat → Int) =>
    And
      (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i n →
          @Eq.{1} Int (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst i))
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
              (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcA i))
              (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) c
                (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB i)))))
      (Light.SameOutside μ μ' dst n) := by
  sorry
