-- Prove2me | Theorems.Thm_ThreeSum_LightReportingBucketTest_meets
-- name    : ThreeSum.LightReportingBucketTest.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:03:56.626072+00:00
-- url     : https://prove2.me/theorems/123fd261-f7a1-48e8-995f-d2ad79021e4e
-- title:
--   Testing original value pairs from independently enabled buckets
-- statement:
--   Suppose memory holds left and right integer arrays $L_i$ ($i<N_L$), $R_j$ ($j<N_R$), and their exact stored bucket layouts for labels $\kappa_L(i),\kappa_R(j)<M$. Choose bucket labels $u,v<M$ and flags $f_L,f_R\in\{0,1\}$. All value, offset, and flat-index arrays end before scratch base $w$. Assume the specified selectors and pair scanner, with $w+4\le S\le B$, $d+2\le D$, and
--   $$|a|,\ |L_i|,\ |R_j|,\ |a+L_i|\le B,\qquad N_LN_R\le B.$$
--   Let $n_L$ and $n_R$ be the selected bucket sizes, each zero when its flag is zero. Within $240n_Ln_R+700$ steps, the routine returns
--   $$\#\{(i,j):i<N_L,\ j<N_R,\ f_L=f_R=1,\ \kappa_L(i)=u,\ \kappa_R(j)=v,\ a+L_i=R_j\}.$$
--   Only the four scratch cells may change.
--
--   This checks the original integer equality over the selected physical pairs.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingBucketTest.lean#L36-L122

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Theorems.Thm_ThreeSum_LightReportingBucketPairs_meets
import Theorems.Thm_ThreeSum_LightSourceBucketSelect_meets
import Theorems.Thm_ThreeSum_SourceBuckets_position_bucket_iff
import Theorems.Thm_ThreeSum_SourceBuckets_position_injective


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightSourceBucketSelect
end ThreeSum.LightSourceBucketSelect
namespace ThreeSum.ReportingHostBucketTest
end ThreeSum.ReportingHostBucketTest
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets

theorem ThreeSum.LightReportingBucketTest.meets : ∀ {lim : Light.Limits} {P : Light.Program}
  {d pMain pSelect pPairs pRow srcL srcR offsetsL offsetsR flatL flatR NL NR M rL rR flagL flagR work : Nat}
  {μ : Nat → Int}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightReportingBucketTest.body pSelect pPairs)))
  (hselect :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pSelect)
      (@Option.some.{0} Light.Stmt ThreeSum.LightSourceBucketSelect.body))
  (hpairs :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pPairs)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightReportingBucketPairs.body pRow)))
  (hrow :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pRow)
      (@Option.some.{0} Light.Stmt ThreeSum.LightReportingBucketRow.body))
  (a : Int) (left right : Nat → Int) (keyL keyR : Nat → Nat)
  (HL : ThreeSum.SourceBuckets.Stored μ keyL NL M offsetsL flatL)
  (HR : ThreeSum.SourceBuckets.Stored μ keyR NR M offsetsR flatR)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      lim.depth)
  (hsrcL : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcL NL) work)
  (hsrcR : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcR NR) work)
  (hoffsetsL :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offsetsL M)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      work)
  (hoffsetsR :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offsetsR M)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      work)
  (hflatL : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flatL NL) work)
  (hflatR : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flatR NR) work)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      lim.space)
  (hkeyL : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i NL → @LT.lt.{0} Nat instLTNat (keyL i) M)
  (hkeyR : ∀ (j : Nat), @LT.lt.{0} Nat instLTNat j NR → @LT.lt.{0} Nat instLTNat (keyR j) M)
  (hrL : @LT.lt.{0} Nat instLTNat rL M) (hrR : @LT.lt.{0} Nat instLTNat rR M)
  (hflagL : @LE.le.{0} Nat instLENat flagL (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hflagR : @LE.le.{0} Nat instLENat flagR (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
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
      (@Nat.cast.{0} Int instNatCastInt (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) NL NR))
      lim.word),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int a
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcL)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcR)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt offsetsL)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flatL)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rL)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flagL)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt offsetsR)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flatR)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rR)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flagR)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt NL)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt NR)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt M)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                  (@List.nil.{0} Int))))))))))))))))
    μ (ThreeSum.LightReportingBucketTest.time keyL keyR NL NR rL rR flagL flagR) fun (r : Int) (ν : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt
          (ThreeSum.ReportingHostBucketTest.testCount μ a left right keyL keyR NL NR flatL flatR rL rR flagL flagR)))
      (Light.SameOutside μ ν work (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) := by
  sorry
