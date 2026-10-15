-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBandStep_tail_ends
-- name    : ThreeSum.LightSourceBandStep.tail_ends
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:29:07.042791+00:00
-- url     : https://prove2.me/theorems/1bdfcfa7-88b4-4773-887c-4946edee5884
-- title:
--   Completing one source-band bucket record
-- statement:
--   Let $g,p,m>0$, and let a stored length-$n$ integer array $f$ have $|f(j)|\le U$. Fix a valid band $i<\lceil n/g\rceil$, with start $s=ig$ and end $t=\min(n,(i+1)g)$, and a shift $|\delta|\le\Delta$. Start the tail body in its specified frame containing these endpoints and the defined packed-band pointers; the source ends before the band-record base.
--
--   Assume the original-source bucket procedures are present, their residue scratch fits space $S$, $S\le W$, $4U+8p+4\Delta+4m+n+g+34\le W$, and $d+3<D$. The output contains the six-field band header and exact code, histogram, and stable bucket arrays for
--   $$\kappa_j=((f(s+j)\bmod p)+\delta)\bmod m\qquad(j<t-s).$$
--   It preserves cells below this band's histogram except its six header cells. Its budget is
--   $$498\min(n,g)(\lfloor\log_2(U+1)\rfloor+\lfloor\log_2(p+\Delta+1)\rfloor+1)+233m+1333.$$
--
--   This completes one packed source band while protecting earlier retained bands.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBandStep.lean#L55-L169

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
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
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
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
import Theorems.Thm_ThreeSum_LightSourceBucketOriginal_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets

theorem ThreeSum.LightSourceBandStep.tail_ends : ∀ {lim : Light.Limits} {P : Light.Program} {d pOriginal : Nat}
  (C : ThreeSum.LightSourceBucketOriginal.Procs P pOriginal) {μ : Nat → Int} {src n g p m base U D i last : Nat}
  {shift : Int} (f : Nat → Int)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      lim.depth)
  (hg : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hm : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
  (hi : @LT.lt.{0} Nat instLTNat i (ThreeSum.BandPartition.size n g))
  (hsrc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) base)
  (hlast : @Eq.{1} Nat last (ThreeSum.BandPartition.stop n g i))
  (hspace :
    @LE.le.{0} Nat instLENat (ThreeSum.LightSourceResidues.space (ThreeSum.SourceBandLayout.work base n g m) p U D)
      lim.space)
  (hshift :
    @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup shift)
      (@Nat.cast.{0} Int instNatCastInt D))
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceBandStep.word n g p m U D))
      lim.word)
  (hread :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src j)) (f j))
  (hvalues :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j n →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (f j))
          (@Nat.cast.{0} Int instNatCastInt U)),
  Light.Ends lim P d (ThreeSum.LightSourceBandStep.tailBody pOriginal)
    {
      loc :=
        Light.frame
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt g)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt m)
                    (@List.cons.{0} Int shift
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt base)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SourceBandLayout.cap n g))
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BandPartition.size n g))
                            (@List.cons.{0} Int
                              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SourceBandLayout.data base n g))
                              (@List.cons.{0} Int
                                (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SourceBandLayout.stride n g m))
                                (@List.cons.{0} Int
                                  (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SourceBandLayout.work base n g m))
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt i)
                                    (@List.cons.{0} Int
                                      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BandPartition.start g i))
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt last)
                                        (@List.nil.{0} Int)))))))))))))))),
      mem := μ }
    (ThreeSum.LightSourceBandStep.tailTime n g p m U D) fun (σ : Light.State) =>
    And (ThreeSum.SourceBandData.At σ.mem f base n g p m shift i)
      (Light.KeptBut μ σ.mem (ThreeSum.SourceBandLayout.hist base n g m i)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) i))
        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) := by
  sorry
