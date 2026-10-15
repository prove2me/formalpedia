-- Prove2me | Theorems.Thm_ThreeSum_LightReportingBucketPairs_meets
-- name    : ThreeSum.LightReportingBucketPairs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:35:28.470156+00:00
-- url     : https://prove2.me/theorems/3903113c-0972-4db7-beb8-9065509dc66c
-- title:
--   Verified counting of exact value matches across two physical buckets
-- statement:
--   Let integer arrays $L,R$ of lengths $N_L,N_R$ be stored at bases $s_L,s_R$. Let natural index arrays $I,J$ of lengths $n_L,n_R$ be stored at $a_L,a_R$, with $I_i<N_L$ and $J_j<N_R$. Assume all four segments lie within machine space $S\le W$, every source value and the fixed integer $a$ have absolute value at most $W$, and $|a+L_i|\le W$ for $i<N_L$. Also assume $n_Ln_R\le W$ and $d<D$. If $P$ contains the bucket-pair counter and its row counter, execution on these arrays and dimensions takes at most $240n_Ln_R+100$ steps and returns
--
--   $$
--   r=|\{(i,j):i<n_L,\ j<n_R,\ R_{J_j}=a+L_{I_i}\}|,\qquad \nu=\mu.
--   $$
--
--   This counts physical matches with their index multiplicities while leaving all memory unchanged.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingBucketPairs.lean#L77-L142

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
import Definitions.Def_ThreeSum1962Source_Bundle04
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
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
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_ThreeSum_LightReportingBucketRow_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightReportingBucketPairs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain pRow srcL srcR indicesL indicesR nL nR NL NR : Nat} {μ : Nat → Int}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightReportingBucketPairs.body pRow)))
  (hrow :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pRow)
      (@Option.some.{0} Light.Stmt ThreeSum.LightReportingBucketRow.body))
  (a : Int) (left right : Nat → Int) (indexL indexR : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth)
  (hsrcL : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcL NL) lim.space)
  (hsrcR : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcR NR) lim.space)
  (hindicesL :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) indicesL nL) lim.space)
  (hindicesR :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) indicesR nR) lim.space)
  (hindexL : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i nL → @LT.lt.{0} Nat instLTNat (indexL i) NL)
  (hindexR : ∀ (j : Nat), @LT.lt.{0} Nat instLTNat j nR → @LT.lt.{0} Nat instLTNat (indexR j) NR)
  (hreadIL :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i nL →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) indicesL i))
          (@Nat.cast.{0} Int instNatCastInt (indexL i)))
  (hreadIR :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j nR →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) indicesR j))
          (@Nat.cast.{0} Int instNatCastInt (indexR j)))
  (hreadL :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i NL →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcL i)) (left i))
  (hreadR :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NR →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcR j)) (right j))
  (hvaluesL :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i NL →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (left i)) lim.word)
  (hvaluesR :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NR →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (right j)) lim.word)
  (ha : @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup a) lim.word)
  (htarget :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i NL →
        @LE.le.{0} Int Int.instLEInt
          (@abs.{0} Int instLatticeInt Int.instAddGroup
            (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) a (left i)))
          lim.word)
  (hcountWord :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) nL nR))
      lim.word),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int a
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcL)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcR)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt indicesL)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt indicesR)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nL)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nR)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt NL)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt NR) (@List.nil.{0} Int))))))))))
    μ (ThreeSum.LightReportingBucketPairs.time nL nR) fun (r : Int) (ν : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightReportingBucketPairs.count a left right indexL indexR nR nL)))
      (@Eq.{1} (Nat → Int) ν μ) := by
  sorry
