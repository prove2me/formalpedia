-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBucketSetup_Procs_meets
-- name    : ThreeSum.LightSourceBucketSetup.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:15:14.941011+00:00
-- url     : https://prove2.me/theorems/de6b16bf-5f84-4629-a13d-86b064785b9d
-- title:
--   Build exact residue buckets from a stored key array
-- statement:
--   Let $N$ stored natural keys $k_i$ lie below a positive residue count $M$, and let the key array end by free address $f$. Assume $f+3M+1+N$ fits in space, space fits in a word, and $d+2$ is below the depth limit. The installed bucket-setup program computes its own histogram, offsets, cursors, and flat-index addresses. It returns
--   $$
--   r=f+3M+1+N,\qquad \mu'(f+j)=|\{i<N:k_i=j\}|\quad(j<M).
--   $$
--   The offset array starts at $f+M$ and the flat original-index array at $f+3M+1$; together they satisfy the exact bucket-storage contract. Memory below $f$ is preserved, and time is the bucket-builder budget plus $200$.
--
--   This supplies reusable physical residue fibers for source and wanted data.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBucketSetup.lean#L43-L71

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
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
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
import Theorems.Thm_ThreeSum_LightSourceBucketBuild_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets

theorem ThreeSum.LightSourceBucketSetup.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (C : ThreeSum.LightSourceBucketSetup.Procs P pMain)
  {μ : Nat → Int} {keys N M base : Nat} (key : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      lim.depth)
  (hM : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) M)
  (hkeys : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keys N) base)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightSourceBucketSetup.next base N M) lim.space)
  (hkey : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i N → @LT.lt.{0} Nat instLTNat (key i) M)
  (hread :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i N →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keys i))
          (@Nat.cast.{0} Int instNatCastInt (key i))),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt keys)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt N)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt M)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt base) (@List.nil.{0} Int)))))
    μ (ThreeSum.LightSourceBucketSetup.time N M) fun (r : Int) (ν : Nat → Int) =>
    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceBucketSetup.next base N M)))
      (And
        (ThreeSum.SourceBuckets.Stored ν key N M (ThreeSum.LightSourceBucketSetup.offsets base M)
          (ThreeSum.LightSourceBucketSetup.flat base M))
        (And
          (∀ (j : Nat),
            @LT.lt.{0} Nat instLTNat j M →
              @Eq.{1} Int
                (ν
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ThreeSum.LightSourceBucketSetup.hist base) j))
                (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightHistogram.count key j N)))
          (Light.Kept μ ν base))) := by
  sorry
