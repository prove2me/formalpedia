-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBucketBuild_Procs_meets
-- name    : ThreeSum.LightSourceBucketBuild.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:04:21.088571+00:00
-- url     : https://prove2.me/theorems/f0f208a8-272d-4a15-b118-abb53f6570f9
-- title:
--   Building stable source buckets directly from a key array
-- statement:
--   Let memory store natural labels $\kappa_i<M$ for $i<N$ at base $k$. Choose histogram, offset, cursor, and flat-index bases $h,o,c,f$. The key and histogram intervals are disjoint, and
--   $$k+N\le o,\quad h+M\le o,\quad o+M+1\le c,\quad c+M\le f,\quad f+N\le S\le B.$$
--   Assume $d+1<D$ and the specified histogram and bucket-building procedures. Within $144N+133M+287$ steps, the routine constructs
--   $$\nu(h+r)=\#\{i<N:\kappa_i=r\},\qquad\nu(o+r)=\#\{i<N:\kappa_i<r\},$$
--   for $r<M$ and $r\le M$, respectively. The flat array stores each index $i$ at position $\#\{j<N:\kappa_j<\kappa_i\}+\#\{j<i:\kappa_j=\kappa_i\}$, preserving source order within every bucket. Only addresses in $[h,f+N)$ may change.
--
--   This derives exact contiguous bucket layouts from the stored codes themselves.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBucketBuild.lean#L35-L69

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
import Theorems.Thm_ThreeSum_LightHistogram_histogram_meets
import Theorems.Thm_ThreeSum_LightSourceBucketFromHistogram_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets

theorem ThreeSum.LightSourceBucketBuild.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (C : ThreeSum.LightSourceBucketBuild.Procs P pMain)
  {μ : Nat → Int} {keys hist offsets cursor flat N M : Nat} (key : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      lim.depth)
  (hkeys : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keys N) offsets)
  (hhist : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist M) offsets)
  (hsep : Light.Apart keys N hist M)
  (hoffsets :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offsets M)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      cursor)
  (hcursor : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cursor M) flat)
  (hspace : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flat N) lim.space)
  (hkey : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i N → @LT.lt.{0} Nat instLTNat (key i) M)
  (hread :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i N →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keys i))
          (@Nat.cast.{0} Int instNatCastInt (key i))),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt keys)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt hist)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt offsets)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cursor)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flat)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt N)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt M) (@List.nil.{0} Int))))))))
    μ (ThreeSum.LightSourceBucketBuild.time N M) fun (x : Int) (ν : Nat → Int) =>
    And (ThreeSum.SourceBuckets.Stored ν key N M offsets flat)
      (And
        (∀ (r : Nat),
          @LT.lt.{0} Nat instLTNat r M →
            @Eq.{1} Int (ν (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist r))
              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightHistogram.count key r N)))
        (And (Light.Kept μ ν hist)
          (Light.SameOutside μ ν hist
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flat N) hist)))) := by
  sorry
