-- Prove2me | Theorems.Thm_ThreeSum_LightClassFilter_meets
-- name    : ThreeSum.LightClassFilter.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:04:41.84489+00:00
-- url     : https://prove2.me/theorems/a13892de-7825-4f12-aefa-ff407cf6cd3e
-- title:
--   Stable filtering and scaling of a chosen color class
-- statement:
--   Let memory $\mu$ contain integer values $x_i$ at $\mathrm{src}$ and colors $c_i\in\{0,1,2\}$ at $\mathrm{colors}$, for $i<n$. Fix a desired color $w<3$, integer scale $s$ with $|s|\le1$, and natural $U$ with $|x_i|\le U\le\mathrm{word}$. Assume $3\le\mathrm{word}$, both input arrays end at or before $\mathrm{dst}$, and $\mathrm{dst}+n+1\le\mathrm{space}\le\mathrm{word}$.
--
--   If the Light program contains the class-filter body, its call on these parameters terminates within $100n+100$ steps. For the list $L=[s x_i\mid i<n,\ c_i=w]$, in increasing input-index order, the result satisfies
--   $$
--   r=|L|,\qquad \nu(\mathrm{dst})=|L|,\qquad
--   \nu(\mathrm{dst}+1+j)=L_j\quad(j<|L|).
--   $$
--   Memory outside $[\mathrm{dst},\mathrm{dst}+n+1)$ is preserved.
--
--   This constructs the selected color-class array with its stored length.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightClassFilter.lean#L59-L127

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
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightClassFilter.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d p src colors dst n want U : Nat} {scale : Int} {μ : Nat → Int}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P p)
      (@Option.some.{0} Light.Stmt ThreeSum.LightClassFilter.body))
  (x : Nat → Int) (color : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (h3 : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))) lim.word)
  (hsrc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) dst)
  (hcolors : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) colors n) dst)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      lim.space)
  (hwant : @LT.lt.{0} Nat instLTNat want (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (hscale :
    @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup scale)
      (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
  (hU : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt U) lim.word)
  (hread :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src i)) (x i))
  (hcolorRead :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) colors i))
          (@Nat.cast.{0} Int instNatCastInt (color i)))
  (hcolorLt :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @LT.lt.{0} Nat instLTNat (color i) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (hbound :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (x i))
          (@Nat.cast.{0} Int instNatCastInt U)),
  Light.Meets lim P p d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt colors)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt want)
              (@List.cons.{0} Int scale (@List.nil.{0} Int)))))))
    μ (ThreeSum.LightClassFilter.time n) fun (r : Int) (ν : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt
          (@List.length.{0} Int (ThreeSum.LightClassFilter.items x color want scale n))))
      (And
        (@Eq.{1} Int (ν dst)
          (@Nat.cast.{0} Int instNatCastInt
            (@List.length.{0} Int (ThreeSum.LightClassFilter.items x color want scale n))))
        (And
          (Light.Seg ν
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (ThreeSum.LightClassFilter.items x color want scale n))
          (Light.SameOutside μ ν dst
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) := by
  sorry
