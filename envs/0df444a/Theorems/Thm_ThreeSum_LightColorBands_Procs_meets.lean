-- Prove2me | Theorems.Thm_ThreeSum_LightColorBands_Procs_meets
-- name    : ThreeSum.LightColorBands.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:37:47.509145+00:00
-- url     : https://prove2.me/theorems/d71249a2-226a-4620-9890-9b368ec8c46e
-- title:
--   Construct normalized color bands and their lookup tables
-- statement:
--   Let $x_i$ ($i<n$) be stored integers with $|x_i|\le U$, and let $p$ be a width-$w$ coloring with $n\le2^w$. Fix a band size $g>0$. Reserve, in order after the input, $n$ color cells, three class buffers of $n+1$ cells, and for each class an $n$-cell normalized-value buffer followed by a $2+2n$-cell endpoint buffer. Scratch follows these areas.
--
--   Assume the specified color and band procedures, $S\le W$, and the exact composite space, word, and depth budgets fit the machine limits. The routine produces strictly increasing lists $A,B,C$ satisfying
--   $$z\in A\iff z\in[x_i:p(i)=0],\quad z\in B\iff z\in[x_i:p(i)=1],\quad z\in C\iff z\in[-x_i:p(i)=2].$$
--   It stores their band headers and endpoints and all three cross-band lookup tables, returning the total table length. Its time is the color-class budget plus the uniform band-preprocessing budget plus $300$, and it preserves memory before the color cells.
--
--   This supplies normalized band data directly from a coloring of the original input.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightColorBands.lean#L55-L127

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_LightBandPreprocessing_Procs_meets
import Theorems.Thm_ThreeSum_LightBandPreprocessing_time_bound
import Theorems.Thm_ThreeSum_LightColorClasses_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress

theorem ThreeSum.LightColorBands.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain src n W colors dst0 dst1 dst2 g av ae bv be cv ce work U : Nat}
  {μ : Nat → Int} (R : ThreeSum.LightColorBands.Procs P pMain) (p : ThreeSum.Coloring.Parameter W) (x : Fin n → Int)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hn :
    @LE.le.{0} Nat instLENat n
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W))
  (hg : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g)
  (hsrc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) colors)
  (hcolors : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) colors n) dst0)
  (h0 :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst0 n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      dst1)
  (h1 :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst1 n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      dst2)
  (h2 :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst2 n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      av)
  (hav : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) av n) ae)
  (hae :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ae
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      bv)
  (hbv : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bv n) be)
  (hbe :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) be
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      cv)
  (hcv : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cv n) ce)
  (hce :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ce
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
      work)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightColorBands.space work W n g) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightColorBands.word W n g U)) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d (ThreeSum.LightColorBands.depth W n g))
      lim.depth)
  (hread : Light.Seg μ src (@List.ofFn.{0} Int n x))
  (hbound :
    ∀ (i : Fin n),
      @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (x i))
        (@Nat.cast.{0} Int instNatCastInt U)),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt W)
          (@List.cons.{0} Int
            (@Nat.cast.{0} Int instNatCastInt
              (@Fin.val W
                (@Prod.fst.{0, 0} (Fin W) (Fin W)
                  (@Prod.fst.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                    (Prod.{0, 0} Bool Bool → Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) p))))
            (@List.cons.{0} Int
              (@Nat.cast.{0} Int instNatCastInt
                (@Fin.val W
                  (@Prod.snd.{0, 0} (Fin W) (Fin W)
                    (@Prod.fst.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                      (Prod.{0, 0} Bool Bool → Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) p))))
              (@List.cons.{0} Int
                (@Nat.cast.{0} Int instNatCastInt
                  (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@Prod.snd.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                      (Prod.{0, 0} Bool Bool → Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) p
                      (@Prod.mk.{0, 0} Bool Bool Bool.false Bool.false))))
                (@List.cons.{0} Int
                  (@Nat.cast.{0} Int instNatCastInt
                    (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      (@Prod.snd.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                        (Prod.{0, 0} Bool Bool → Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) p
                        (@Prod.mk.{0, 0} Bool Bool Bool.false Bool.true))))
                  (@List.cons.{0} Int
                    (@Nat.cast.{0} Int instNatCastInt
                      (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@Prod.snd.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                          (Prod.{0, 0} Bool Bool → Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) p
                          (@Prod.mk.{0, 0} Bool Bool Bool.true Bool.false))))
                    (@List.cons.{0} Int
                      (@Nat.cast.{0} Int instNatCastInt
                        (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Prod.snd.{0, 0} (Prod.{0, 0} (Fin W) (Fin W))
                            (Prod.{0, 0} Bool Bool → Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            p (@Prod.mk.{0, 0} Bool Bool Bool.true Bool.true))))
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt colors)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst0)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst1)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst2)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt g)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt av)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt ae)
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bv)
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt be)
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cv)
                                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt ce)
                                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                                              (@List.nil.{0} Int))))))))))))))))))))))
    μ (ThreeSum.LightColorBands.time W n g) fun (r : Int) (ν : Nat → Int) =>
    And
      (ThreeSum.LightBandPreprocessing.Output ν av ae bv be cv ce work g hg
        (@ThreeSum.ColorClassLists.classList n W p x (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@ThreeSum.ColorClassLists.classList n W p x (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@ThreeSum.ColorClassLists.classList n W p x (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
        r)
      (Light.Kept μ ν colors) := by
  sorry
