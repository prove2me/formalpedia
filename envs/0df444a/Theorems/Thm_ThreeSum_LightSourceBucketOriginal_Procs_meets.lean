-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBucketOriginal_Procs_meets
-- name    : ThreeSum.LightSourceBucketOriginal.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:17:15.67927+00:00
-- url     : https://prove2.me/theorems/89a90d1f-b386-4411-8a07-e5523ef28c60
-- title:
--   Bucket original signed values by their shifted double residues
-- statement:
--   Let $x_i=\mu(s+i)$ for $i<N$, with $|x_i|\le U$. Take positive moduli $p,m$ and a shift $\sigma$ with $|\sigma|\le D$. In memory order, reserve the source, $m$ histogram cells, $N$ codes, $m+1$ offsets, $m$ cursors, $N$ flat indices, and residue scratch. Assume the stated residue workspace fits, space fits in a word, $4U+8p+4D+4m+32$ fits in a word, and $d+2$ is below the depth limit. The installed program constructs keys
--   $$
--   k_i=((x_i\bmod p)+\sigma)\bmod m
--   $$
--   and stores every code, the exact histogram $H_r=|\{i<N:k_i=r\}|$, and the offset/flat-index representation of these buckets. It preserves memory below the histogram base within its histogram-plus-bucket time budget.
--
--   The retained buckets refer to original source positions.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBucketOriginal.lean#L35-L79

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
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_LightSourceBucketFromHistogram_Procs_meets
import Theorems.Thm_ThreeSum_LightSourceHistogram_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets

theorem ThreeSum.LightSourceBucketOriginal.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (C : ThreeSum.LightSourceBucketOriginal.Procs P pMain)
  {μ : Nat → Int} {src N p m hist codes offsets cursor flat work U D : Nat} {shift : Int}
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      lim.depth)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hm : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
  (hsrc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src N) hist)
  (hhist : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist m) codes)
  (hcodes : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) codes N) offsets)
  (hoffsets :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offsets m)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      cursor)
  (hcursor : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cursor m) flat)
  (hflat : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flat N) work)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightSourceResidues.space work p U D) lim.space)
  (hshift :
    @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup shift)
      (@Nat.cast.{0} Int instNatCastInt D))
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceResidues.word p m U D))
      lim.word)
  (hvalues :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i N →
        @LE.le.{0} Int Int.instLEInt
          (@abs.{0} Int instLatticeInt Int.instAddGroup
            (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src i)))
          (@Nat.cast.{0} Int instNatCastInt U)),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt N)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt m)
            (@List.cons.{0} Int shift
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt hist)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt codes)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt offsets)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cursor)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flat)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work) (@List.nil.{0} Int))))))))))))
    μ (ThreeSum.LightSourceBucketOriginal.time N p m U D) fun (x : Int) (ν : Nat → Int) =>
    And
      (ThreeSum.SourceBuckets.Stored ν
        (fun (i : Nat) =>
          ThreeSum.LightSourceResidues.key p m shift
            (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src i)))
        N m offsets flat)
      (And
        (∀ (r : Nat),
          @LT.lt.{0} Nat instLTNat r m →
            @Eq.{1} Int (ν (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist r))
              (@Nat.cast.{0} Int instNatCastInt
                (ThreeSum.LightHistogram.count
                  (fun (i : Nat) =>
                    ThreeSum.LightSourceResidues.key p m shift
                      (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src i)))
                  r N)))
        (And
          (∀ (i : Nat),
            @LT.lt.{0} Nat instLTNat i N →
              @Eq.{1} Int (ν (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) codes i))
                (@Nat.cast.{0} Int instNatCastInt
                  (ThreeSum.LightSourceResidues.key p m shift
                    (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src i)))))
          (Light.Kept μ ν hist))) := by
  sorry
