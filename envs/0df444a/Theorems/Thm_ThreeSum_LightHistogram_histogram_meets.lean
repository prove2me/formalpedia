-- Prove2me | Theorems.Thm_ThreeSum_LightHistogram_histogram_meets
-- name    : ThreeSum.LightHistogram.histogram_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:33:47.482644+00:00
-- url     : https://prove2.me/theorems/43029af6-8556-483d-a41f-a97c5bc19875
-- title:
--   Verified histogram construction from an arbitrary key array
-- statement:
--   Let $k_i<p$ for $i<n$, and suppose integer memory $\mu$ stores these natural keys at base $a$. Let $z$ be a histogram base such that the segments $[a,a+n)$ and $[z,z+p)$ are disjoint and both lie within machine space $S$. Assume $S\le W$ for word bound $W$ and starting depth $d<D$. If $P$ contains the histogram body and zero-fill helper, execution on $(a,z,n,p)$ finishes within $24n+13p+17$ steps with
--
--   $$
--   \mu'(z+r)=|\{i<n:k_i=r\}|\quad(r<p).
--   $$
--
--   Every cell outside the histogram is preserved. No initial contents of the destination are assumed.
--
--   This supplies exact bucket counts, including the multiplicity of equal keys.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightHistogram.lean#L103-L127

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
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
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
import Theorems.Thm_Light_Ends_pass
import Theorems.Thm_ThreeSum_LightHistogram_count_ends


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightHistogram.histogram_meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pHist pFill : Nat}
  (hp :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pHist)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightHistogram.histogramBody pFill)))
  (hfill :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pFill)
      (@Option.some.{0} Light.Stmt Light.fillBody))
  {μ : Nat → Int} {src dst n p : Nat} (key : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hdepth : @LT.lt.{0} Nat instLTNat d lim.depth)
  (hS : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) lim.space)
  (hD : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst p) lim.space)
  (hsep : Light.Apart src n dst p)
  (hkeys :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src i))
          (@Nat.cast.{0} Int instNatCastInt (key i)))
  (hkeyLt : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i n → @LT.lt.{0} Nat instLTNat (key i) p),
  Light.Meets lim P pHist d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p) (@List.nil.{0} Int)))))
    μ (ThreeSum.LightHistogram.histogramTime n p) fun (x : Int) (μ' : Nat → Int) =>
    And
      (∀ (r : Nat),
        @LT.lt.{0} Nat instLTNat r p →
          @Eq.{1} Int (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst r))
            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightHistogram.count key r n)))
      (Light.SameOutside μ μ' dst p) := by
  sorry
