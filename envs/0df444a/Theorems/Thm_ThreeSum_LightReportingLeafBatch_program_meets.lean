-- Prove2me | Theorems.Thm_ThreeSum_LightReportingLeafBatch_program_meets
-- name    : ThreeSum.LightReportingLeafBatch.program_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:28:54.505553+00:00
-- url     : https://prove2.me/theorems/c4d241cc-ed3e-451f-af9d-72e1335c1fef
-- title:
--   Testing a batch of terminal candidates with exact pair charges
-- statement:
--   Memory stores original arrays $L_i$ ($i<N_L$), $R_j$ ($j<N_R$), their exact buckets with labels below $M>0$, and $n$ endpoint pairs $(x_s,y_s)$ with independent Boolean flags $(f_s,g_s)$. All inputs end before scratch $w$. Assume $|x_s|,|y_s|\le U$, $|a|,|L_i|,|R_j|,|a+L_i|\le W$, $N_LN_R\le W$, and
--   $$w+\lfloor\log_2(U+1)\rfloor+6\le S\le W,\quad4U+4M+16\le W,\quad d+n+4\le D.$$
--   The fixed program returns $r\in\{0,1\}$ with
--   $$r=1\iff\exists s<n,\ i<N_L,\ j<N_R:\ f_s=g_s=1,\ \kappa_L(i)=x_s\bmod M,\ \kappa_R(j)=y_s\bmod M,\ a+L_i=R_j.$$
--   Cells below $w$ are preserved. If $b_s,c_s$ are the independently enabled bucket sizes, its budget is $30+\sum_{s<n}[240b_sc_s+2R(U)+1300]$, where $R(U)=43(\lfloor\log_2(U+1)\rfloor+1)+34$.
--
--   The scan charges each candidate by its actual selected pair mass.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingLeafBatch.lean#L69-L156

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
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
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
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
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
import Theorems.Thm_ThreeSum_LightReportingLeaf_program_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.ReportingHostBucketTest
end ThreeSum.ReportingHostBucketTest
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets

theorem ThreeSum.LightReportingLeafBatch.program_meets : ∀ {lim : Light.Limits} {μ : Nat → Int}
  {srcL srcR offsetsL offsetsR flatL flatR NL NR Mo rawL rawR flagsL flagsR n work U d : Nat} (a : Int)
  (xL xR left right : Nat → Int) (keyL keyR flagL flagR : Nat → Nat)
  (HL : ThreeSum.SourceBuckets.Stored μ keyL NL Mo offsetsL flatL)
  (HR : ThreeSum.SourceBuckets.Stored μ keyR NR Mo offsetsR flatR)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d n)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      lim.depth)
  (hMo : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) Mo)
  (hsrcL : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcL NL) work)
  (hsrcR : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcR NR) work)
  (hoffsetsL :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offsetsL Mo)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      work)
  (hoffsetsR :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offsetsR Mo)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      work)
  (hflatL : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flatL NL) work)
  (hflatR : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flatR NR) work)
  (hrawL : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawL n) work)
  (hrawR : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawR n) work)
  (hflagsL : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagsL n) work)
  (hflagsR : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagsR n) work)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (Nat.log (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) U
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) (@Nat.cast.{0} Int instNatCastInt U))
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) (@Nat.cast.{0} Int instNatCastInt Mo)))
        (@OfNat.ofNat.{0} Int (nat_lit 16) (@instOfNat (nat_lit 16))))
      lim.word)
  (hkeyL : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i NL → @LT.lt.{0} Nat instLTNat (keyL i) Mo)
  (hkeyR : ∀ (j : Nat), @LT.lt.{0} Nat instLTNat j NR → @LT.lt.{0} Nat instLTNat (keyR j) Mo)
  (hflagL :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @LE.le.{0} Nat instLENat (flagL i) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hflagR :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @LE.le.{0} Nat instLENat (flagR i) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hreadL :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i NL →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcL i)) (left i))
  (hreadR :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NR →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcR j)) (right j))
  (hreadXL :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawL i)) (xL i))
  (hreadXR :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rawR i)) (xR i))
  (hreadFL :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagsL i))
          (@Nat.cast.{0} Int instNatCastInt (flagL i)))
  (hreadFR :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagsR i))
          (@Nat.cast.{0} Int instNatCastInt (flagR i)))
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
  (hxL :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (xL i))
          (@Nat.cast.{0} Int instNatCastInt U))
  (hxR :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (xR i))
          (@Nat.cast.{0} Int instNatCastInt U))
  (hcountWord :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) NL NR))
      lim.word),
  Light.Meets lim ThreeSum.LightReportingLeafBatch.program (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
    d
    (@List.cons.{0} Int a
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcL)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcR)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt offsetsL)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flatL)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt offsetsR)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flatR)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt NL)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt NR)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt Mo)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rawL)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rawR)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flagsL)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flagsR)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                    (@List.nil.{0} Int)))))))))))))))))
    μ (ThreeSum.LightReportingLeafBatch.time keyL keyR flagL flagR NL NR Mo U xL xR n) fun (r : Int) (ν : Nat → Int) =>
    And
      (Or (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      (And
        (Iff (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (ThreeSum.LightReportingLeafBatch.Hit a xL xR left right keyL keyR flagL flagR NL NR Mo n))
        (Light.Kept μ ν work)) := by
  sorry
