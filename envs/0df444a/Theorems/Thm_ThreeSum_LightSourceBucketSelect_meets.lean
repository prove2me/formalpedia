-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBucketSelect_meets
-- name    : ThreeSum.LightSourceBucketSelect.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:25:52.379971+00:00
-- url     : https://prove2.me/theorems/744cdbe7-45d8-4e79-9007-174f79e70ae0
-- title:
--   Verified bucket selection with an independent flag
-- statement:
--   Let memory $\mu$ contain the stored bucket representation of $N$ keys, each below $M$, with offset-array base $o$ and flat-index base $f$. Let $r<M$, let $\varepsilon\in\{0,1\}$, and let $z$ be the two-cell output base. Assume $o+M+1\le z$, $f+N\le z$, $z+2\le S$, and $S\le W$, where $S,W$ are the machine space and word bounds. Suppose the called procedure in $P$ is the bucket-selection body. At any call depth, it terminates within $120$ steps with
--
--   $$
--   \nu(z)=f+O(r),\qquad\nu(z+1)=\varepsilon C(r),\qquad\nu(a)=\mu(a)\quad(a\notin[z,z+2)),
--   $$
--
--   where $C(r)$ counts keys equal to $r$ and $O(r)=\sum_{s<r}C(s)$. This exposes the bucket's address and flag-controlled count while preserving all other cells.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBucketSelect.lean#L51-L99

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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets

theorem ThreeSum.LightSourceBucketSelect.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt ThreeSum.LightSourceBucketSelect.body))
  {μ : Nat → Int} {key : Nat → Nat} {N M offsets flat r flag dst : Nat}
  (H : ThreeSum.SourceBuckets.Stored μ key N M offsets flat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hoffsets :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offsets M)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      dst)
  (hflat : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flat N) dst)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      lim.space)
  (hkey : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i N → @LT.lt.{0} Nat instLTNat (key i) M)
  (hr : @LT.lt.{0} Nat instLTNat r M)
  (_hflag : @LE.le.{0} Nat instLENat flag (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt offsets)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flat)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt r)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt flag)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt M)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt N) (@List.nil.{0} Int))))))))
    μ (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))) fun (x : Int) (ν : Nat → Int) =>
    And
      (@Eq.{1} Int (ν dst)
        (@Nat.cast.{0} Int instNatCastInt
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flat
            (ThreeSum.SourceBuckets.offset key N r))))
      (And
        (@Eq.{1} Int
          (ν
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceBucketSelect.countSelected key N r flag)))
        (Light.SameOutside μ ν dst (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  sorry
