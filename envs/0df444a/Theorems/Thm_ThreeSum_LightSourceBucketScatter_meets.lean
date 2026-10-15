-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBucketScatter_meets
-- name    : ThreeSum.LightSourceBucketScatter.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:05:16.403752+00:00
-- url     : https://prove2.me/theorems/a3cf29a9-15ca-4858-8861-606c1307ee9c
-- title:
--   Verified stable scatter into source-key buckets
-- statement:
--   Let $N,M$ be natural numbers and $k_i<M$ for $i<N$. Define $c_r(t)=|\{i<t:k_i=r\}|$, $O(r)=\sum_{u<r}c_u(N)$, and $\pi(i)=O(k_i)+c_{k_i}(i)$. In integer memory $\mu$, suppose the key array at $a$ stores $k_i$ and the cursor array at $c$ initially stores $O(r)$. Let $f$ be the flat-output base, with $a+N\le c$, $c+M\le f$, and $f+N\le S\le W$, where $S,W$ are the machine space and word bounds. If the called procedure in $P$ is the scatter body, execution on $(a,c,f,N,M)$ at any depth takes at most $120N+20$ steps and produces memory $\nu$ satisfying
--
--   $$
--   \nu(f+\pi(i))=i\ (i<N),\qquad \nu(c+r)=O(r+1)\ (r<M).
--   $$
--
--   Memory outside $[c,f+N)$ is preserved. This supplies the stable index layout used by subsequent source-bucket scans.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBucketScatter.lean#L35-L107

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
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_ThreeSum_SourceBuckets_position_injective


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightSourceBucketScatter.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt ThreeSum.LightSourceBucketScatter.body))
  {μ : Nat → Int} {keys cursor flat N M : Nat} (key : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hkeys : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keys N) cursor)
  (hcursor : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cursor M) flat)
  (hspace : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flat N) lim.space)
  (hkey : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i N → @LT.lt.{0} Nat instLTNat (key i) M)
  (hread :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i N →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keys i))
          (@Nat.cast.{0} Int instNatCastInt (key i)))
  (hzero :
    ∀ (r : Nat),
      @LT.lt.{0} Nat instLTNat r M →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cursor r))
          (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SourceBuckets.offset key N r))),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt keys)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cursor)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flat)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt N)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt M) (@List.nil.{0} Int))))))
    μ (ThreeSum.LightSourceBucketScatter.time N) fun (x : Int) (ν : Nat → Int) =>
    And
      (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i N →
          @Eq.{1} Int
            (ν
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flat
                (ThreeSum.SourceBuckets.position key N i)))
            (@Nat.cast.{0} Int instNatCastInt i))
      (And
        (∀ (r : Nat),
          @LT.lt.{0} Nat instLTNat r M →
            @Eq.{1} Int (ν (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cursor r))
              (@Nat.cast.{0} Int instNatCastInt
                (ThreeSum.SourceBuckets.offset key N
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        (Light.SameOutside μ ν cursor
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flat N) cursor))) := by
  sorry
