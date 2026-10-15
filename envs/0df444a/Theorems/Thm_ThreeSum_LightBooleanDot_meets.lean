-- Prove2me | Theorems.Thm_ThreeSum_LightBooleanDot_meets
-- name    : ThreeSum.LightBooleanDot.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:04:32.17098+00:00
-- url     : https://prove2.me/theorems/7570d194-4486-4690-add2-b612f14b7d04
-- title:
--   Verified dot product of Boolean-valued arrays
-- statement:
--   Let $f,g:\mathbb N\to\mathbb N$ satisfy $f(i),g(i)\le1$ for $i<n$, and suppose initial memory $\mu$ stores them at addresses $A,B$. Assume $A+n,B+n\le\mathrm{space}\le\mathrm{word}$, $1\le\mathrm{word}$, and the Light program contains the dot-product body.
--
--   The call with arguments $(A,B,n)$ terminates within $32n+20$ steps and returns
--   $$
--   r=\sum_{i=0}^{n-1}f(i)g(i),\qquad \nu=\mu.
--   $$
--   Thus the result counts positions at which both arrays equal one. This supplies an exact overlap count without modifying either array or any other memory cell.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBooleanDot.lean#L48-L90

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
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightBooleanDot.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d p : Nat}
  (hp :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt ThreeSum.LightBooleanDot.body))
  {μ : Nat → Int} {srcA srcB n : Nat} (f g : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hA : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcA n) lim.space)
  (hB : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB n) lim.space)
  (hreadA :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcA i))
          (@Nat.cast.{0} Int instNatCastInt (f i)))
  (hreadB :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB i))
          (@Nat.cast.{0} Int instNatCastInt (g i)))
  (hf :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @LE.le.{0} Nat instLENat (f i) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hg :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @LE.le.{0} Nat instLENat (g i) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hword : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))) lim.word),
  Light.Meets lim P p d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcA)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcB)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n) (@List.nil.{0} Int))))
    μ (ThreeSum.LightBooleanDot.time n) fun (r : Int) (μ' : Nat → Int) =>
    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBooleanDot.dot f g n)))
      (@Eq.{1} (Nat → Int) μ' μ) := by
  sorry
