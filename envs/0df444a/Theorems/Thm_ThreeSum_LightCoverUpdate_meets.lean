-- Prove2me | Theorems.Thm_ThreeSum_LightCoverUpdate_meets
-- name    : ThreeSum.LightCoverUpdate.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:32:40.474521+00:00
-- url     : https://prove2.me/theorems/a8c00fda-0b88-41e4-98c1-0af6de04b71b
-- title:
--   Removing newly covered entries from an active Boolean row
-- statement:
--   Let $c_i,a_i\in\{0,1\}$, $i<n$, be a cover row and active-target row stored in memory $\mu$ at $C,A$. Assume their length-$n$ intervals are disjoint and fit within $\mathrm{space}\le\mathrm{word}$, with $1\le\mathrm{word}$, and the Light program contains the cover-update body.
--
--   The call with $(C,A,n)$ terminates within $26n+6$ steps and produces
--   $$
--   \nu(A+i)=a_i(1-c_i)\quad(i<n),\qquad
--   \nu(x)=\mu(x)\quad\bigl(x\notin[A,A+n)\bigr).
--   $$
--   Thus an active entry remains active exactly when the chosen row does not cover it. This is the update operation in the finite greedy cover construction.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightCoverUpdate.lean#L17-L52

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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightCoverUpdate.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d p : Nat}
  (hp :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt ThreeSum.LightCoverUpdate.body))
  {μ : Nat → Int} {row activePtr n : Nat} (cover active : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hrow : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) row n) lim.space)
  (hactive :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) activePtr n) lim.space)
  (hsep : Light.Apart row n activePtr n)
  (hread :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) row j))
          (@Nat.cast.{0} Int instNatCastInt (cover j)))
  (hreadActive :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) activePtr j))
          (@Nat.cast.{0} Int instNatCastInt (active j)))
  (hcover :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j n →
        @LE.le.{0} Nat instLENat (cover j) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hact :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j n →
        @LE.le.{0} Nat instLENat (active j) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hword : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))) lim.word),
  Light.Meets lim P p d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt row)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt activePtr)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n) (@List.nil.{0} Int))))
    μ (ThreeSum.LightCoverUpdate.time n) fun (x : Int) (μ' : Nat → Int) =>
    And
      (∀ (j : Nat),
        @LT.lt.{0} Nat instLTNat j n →
          @Eq.{1} Int (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) activePtr j))
            (@Nat.cast.{0} Int instNatCastInt
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (active j)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (cover j)))))
      (Light.SameOutside μ μ' activePtr n) := by
  sorry
