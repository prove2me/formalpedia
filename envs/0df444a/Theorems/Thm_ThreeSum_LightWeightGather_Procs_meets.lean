-- Prove2me | Theorems.Thm_ThreeSum_LightWeightGather_Procs_meets
-- name    : ThreeSum.LightWeightGather.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:33:36.65699+00:00
-- url     : https://prove2.me/theorems/185950cb-467f-4a0a-98c1-54e1f13a345e
-- title:
--   Gathering selected fixed-width coefficient rows
-- statement:
--   Suppose a Light program contains the row-gather body and its copy subroutine. Let a table of $N$ rows of width $W$ start at $A$, and let $s_i<N$, $i<R$, be selection indices stored at $I$. Assume $I+R,A+NW\le D$, $D+RW\le\mathrm{space}\le\mathrm{word}$, $N+R+W+1\le\mathrm{word}$, and $d<\mathrm{depth}$.
--
--   The call with $(I,A,D,R,W)$ terminates within $R(16W+106)+6$ steps and satisfies
--   $$
--   \nu(D+iW+j)=\mu(A+s_iW+j)\quad(i<R,\ j<W),
--   $$
--   while preserving memory outside $[D,D+RW)$.
--
--   This copies the selected coefficient rows in occurrence order, including repeated selections.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightWeightGather.lean#L39-L105

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
import Definitions.Def_ThreeSum1962Source_Bundle03
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
import Theorems.Thm_Light_Ends_pass


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightWeightGather.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightWeightGather.Procs P pMain)
  {μ : Nat → Int} {indices src dst N rows width : Nat} (select : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth)
  (hindices :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) indices rows) dst)
  (hsrc :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) N width))
      dst)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) rows width))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightWeightGather.word N rows width))
      lim.word)
  (hselect : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i rows → @LT.lt.{0} Nat instLTNat (select i) N)
  (hread :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i rows →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) indices i))
          (@Nat.cast.{0} Int instNatCastInt (select i))),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt indices)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rows)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt width) (@List.nil.{0} Int))))))
    μ (ThreeSum.LightWeightGather.time rows width) fun (x : Int) (μ' : Nat → Int) =>
    And
      (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i rows →
          ∀ (a : Nat),
            @LT.lt.{0} Nat instLTNat a width →
              @Eq.{1} Int
                (μ'
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i width))
                    a))
                (μ
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (select i) width))
                    a)))
      (Light.SameOutside μ μ' dst (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) rows width)) := by
  sorry
