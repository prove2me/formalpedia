-- Prove2me | Theorems.Thm_ThreeSum_LightCoverScores_meets
-- name    : ThreeSum.LightCoverScores.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:32:39.715744+00:00
-- url     : https://prove2.me/theorems/328cd8fb-9369-49fd-b958-2ce73d6eca80
-- title:
--   Verified computation of negative greedy-cover row scores
-- statement:
--   Let $A_{ij},v_j\in\{0,1\}$ be a matrix with $r$ rows and $c$ columns and an active-column vector. Suppose integer memory $\mu$ stores them at bases $a$ and $b$, respectively. Let $z$ be the score destination, with $a+rc\le z$, $b+c\le z$, and $z+r\le S\le W$, where $S,W$ are the machine space and word bounds; also assume $1\le W$ and starting depth $d<D$. If program $P$ contains the score constructor and Boolean-dot helper, execution on $(a,b,z,c,r)$ takes at most $r(32c+90)+6$ steps and produces
--
--   $$
--   \mu'(z+i)=-\sum_{j<c}A_{ij}v_j\quad(i<r).
--   $$
--
--   Memory outside $[z,z+r)$ is preserved. Negative scores let the minimum-selection routine choose a row covering the most active targets.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightCoverScores.lean#L34-L101

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
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
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
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_ThreeSum_LightBooleanDot_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightCoverScores.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain pDot : Nat}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightCoverScores.body pDot)))
  (hdot :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pDot)
      (@Option.some.{0} Light.Stmt ThreeSum.LightBooleanDot.body))
  {μ : Nat → Int} {src activePtr dst rows cols : Nat} (matrix : Nat → Nat → Nat) (active : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth)
  (hsrc :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) rows cols))
      dst)
  (hactive :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) activePtr cols) dst)
  (hspace :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst rows) lim.space)
  (hread :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i rows →
        ∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat j cols →
            @Eq.{1} Int
              (μ
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i cols))
                  j))
              (@Nat.cast.{0} Int instNatCastInt (matrix i j)))
  (hreadActive :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j cols →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) activePtr j))
          (@Nat.cast.{0} Int instNatCastInt (active j)))
  (hmatrix :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i rows →
        ∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat j cols →
            @LE.le.{0} Nat instLENat (matrix i j) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hactiveValue :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j cols →
        @LE.le.{0} Nat instLENat (active j) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hword : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))) lim.word),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt activePtr)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cols)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rows) (@List.nil.{0} Int))))))
    μ (ThreeSum.LightCoverScores.time rows cols) fun (x : Int) (μ' : Nat → Int) =>
    And
      (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i rows →
          @Eq.{1} Int (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst i))
            (@Neg.neg.{0} Int Int.instNegInt
              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightCoverScores.score matrix active cols i))))
      (Light.SameOutside μ μ' dst rows) := by
  sorry
