-- Prove2me | Theorems.Thm_ThreeSum_LightHistogram_count_ends
-- name    : ThreeSum.LightHistogram.count_ends
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:04:45.270161+00:00
-- url     : https://prove2.me/theorems/86415590-9a61-4812-a71c-8d0fdf7ab06e
-- title:
--   Verified histogram counting into a zeroed array
-- statement:
--   Let $k:\mathbb N\to\mathbb N$ satisfy $k(i)<p$ for $i<n$. Suppose memory $\mu$ stores these keys in $[\mathrm{src},\mathrm{src}+n)$, and all $p$ cells beginning at $\mathrm{dst}$ are zero. Assume the source and destination intervals are disjoint and fit within $\mathrm{space}\le\mathrm{word}$. The initial locals numbered $0,1,2$ must hold $\mathrm{src},\mathrm{dst},n$.
--
--   In any program and depth context, the Light histogram-count body terminates within $24n+6$ steps and yields
--   $$
--   \nu(\mathrm{dst}+r)=\bigl|\{i<n:k(i)=r\}\bigr|\quad(r<p),
--   $$
--   with $\nu(a)=\mu(a)$ outside $[\mathrm{dst},\mathrm{dst}+p)$.
--
--   This certifies the counting phase of a bucket histogram once the destination has been zeroed.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightHistogram.lean#L45-L96

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
import Theorems.Thm_Light_Ends_for


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightHistogram.count_ends : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {μ loc : Nat → Int} {src dst n p : Nat} (key : Nat → Nat)
  (hsrc :
    @Eq.{1} Int (loc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Nat.cast.{0} Int instNatCastInt src))
  (hdst :
    @Eq.{1} Int (loc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Nat.cast.{0} Int instNatCastInt dst))
  (hlen :
    @Eq.{1} Int (loc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Nat.cast.{0} Int instNatCastInt n))
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hS : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) lim.space)
  (hD : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst p) lim.space)
  (hsep : Light.Apart src n dst p)
  (hkeys :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src i))
          (@Nat.cast.{0} Int instNatCastInt (key i)))
  (hkeyLt : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i n → @LT.lt.{0} Nat instLTNat (key i) p)
  (hzero :
    ∀ (r : Nat),
      @LT.lt.{0} Nat instLTNat r p →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst r))
          (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))),
  Light.Ends lim P d ThreeSum.LightHistogram.countBody { loc := loc, mem := μ } (ThreeSum.LightHistogram.countTime n)
    fun (σ' : Light.State) =>
    And
      (∀ (r : Nat),
        @LT.lt.{0} Nat instLTNat r p →
          @Eq.{1} Int (σ'.mem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst r))
            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightHistogram.count key r n)))
      (Light.SameOutside μ σ'.mem dst p) := by
  sorry
