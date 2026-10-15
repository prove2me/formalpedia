-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBucketOffsets_meets
-- name    : ThreeSum.LightSourceBucketOffsets.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:05:07.324997+00:00
-- url     : https://prove2.me/theorems/1ac78613-8172-403e-9336-0c4be4ed4758
-- title:
--   Verified construction of bucket offsets and insertion cursors
-- statement:
--   Let $k(i)<M$ for $i<N$, and suppose memory $\mu$ stores the exact histogram $H_r=|\{i<N:k(i)=r\}|$ at address $A$. Let offsets begin at $B$ and cursors at $C$, with $A+M\le B$, $B+M+1\le C$, and $C+M\le\mathrm{space}\le\mathrm{word}$. Assume $N\le\mathrm{word}$ and the Light program contains the bucket-offset body.
--
--   Define $O_r=\sum_{q<r}H_q$. The call with arguments $(A,B,C,M,N)$ terminates within $120M+120$ steps and satisfies
--   $$
--   \nu(B+r)=O_r\quad(r\le M),\qquad
--   \nu(C+r)=O_r\quad(r<M).
--   $$
--   Memory outside $[B,C+M)$ is preserved.
--
--   This initializes each bucket's starting offset and insertion cursor, including the final offset after the last bucket.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBucketOffsets.lean#L36-L113

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

theorem ThreeSum.LightSourceBucketOffsets.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt ThreeSum.LightSourceBucketOffsets.body))
  {μ : Nat → Int} {hist offsets cursor M N : Nat} (key : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hN : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt N) lim.word)
  (hhist : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist M) offsets)
  (hoffsets :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offsets M)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      cursor)
  (hspace :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cursor M) lim.space)
  (hkey : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i N → @LT.lt.{0} Nat instLTNat (key i) M)
  (hread :
    ∀ (r : Nat),
      @LT.lt.{0} Nat instLTNat r M →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hist r))
          (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightHistogram.count key r N))),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt hist)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt offsets)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cursor)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt M)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt N) (@List.nil.{0} Int))))))
    μ (ThreeSum.LightSourceBucketOffsets.time M) fun (x : Int) (ν : Nat → Int) =>
    And
      (∀ (r : Nat),
        @LE.le.{0} Nat instLENat r M →
          @Eq.{1} Int (ν (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offsets r))
            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SourceBuckets.offset key N r)))
      (And
        (∀ (r : Nat),
          @LT.lt.{0} Nat instLTNat r M →
            @Eq.{1} Int (ν (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cursor r))
              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SourceBuckets.offset key N r)))
        (Light.SameOutside μ ν offsets
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cursor M) offsets))) := by
  sorry
