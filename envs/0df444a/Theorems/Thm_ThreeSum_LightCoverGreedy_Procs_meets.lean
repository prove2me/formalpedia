-- Prove2me | Theorems.Thm_ThreeSum_LightCoverGreedy_Procs_meets
-- name    : ThreeSum.LightCoverGreedy.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:49:15.497183+00:00
-- url     : https://prove2.me/theorems/a8c00397-a669-47f2-8bde-48b1f660af39
-- title:
--   Executing the finite greedy cover schedule exactly
-- statement:
--   Let a stored $r\times c$ matrix $A$ have entries in $\{0,1\}$ and $r>0$. Starting with all $c$ columns active, choose at each round the least row index maximizing the number of active columns it covers, then deactivate those covered columns. Let $g_0,\ldots,g_{t-1}$ and $U_t$ be the resulting choices and remaining active set.
--
--   Assume the specified fill, score-selection, and update procedures. The source matrix ends before scratch base $a$, and
--   $$a+c+r+t\le S\le B,\quad1\le B,\quad d+2<D.$$
--   The routine returns $o=a+c+r$ and writes
--   $$\nu(o+i)=g_i\ (i<t),\qquad\nu(a+j)=\mathbf1_{j\in U_t}\ (j<c).$$
--   It preserves every cell outside $[a,a+c+r+t)$ and terminates within
--   $$13c+106+t(32rc+122r+26c+300)$$
--   steps.
--
--   This realizes the precise finite greedy schedule, including its tie-breaking and repeated choices.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightCoverGreedy.lean#L62-L180

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_Light_Ends_pass
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons
import Theorems.Thm_ThreeSum_BooleanGreedy_active_succ
import Theorems.Thm_ThreeSum_BooleanGreedy_choice_eq_least
import Theorems.Thm_ThreeSum_LightCoverScores_meets
import Theorems.Thm_ThreeSum_LightCoverUpdate_meets
import Theorems.Thm_ThreeSum_LightMinimum_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BooleanGreedy
end ThreeSum.BooleanGreedy
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightCoverGreedy.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (S : ThreeSum.LightCoverGreedy.Procs P pMain) {μ : Nat → Int}
  {src activePtr rows cols rounds : Nat} (matrix : Nat → Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      lim.depth)
  (hrows : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) rows)
  (hsrc :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) rows cols))
      activePtr)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) activePtr
        (ThreeSum.LightCoverGreedy.total rows cols rounds))
      lim.space)
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
  (hmatrix :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i rows →
        ∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat j cols →
            @LE.le.{0} Nat instLENat (matrix i j) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (hword : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))) lim.word),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt activePtr)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rows)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cols)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rounds) (@List.nil.{0} Int))))))
    μ (ThreeSum.LightCoverGreedy.time rows cols rounds) fun (r : Int) (μ' : Nat → Int) =>
    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightCoverGreedy.out activePtr rows cols)))
      (And
        (Light.Seg μ' (ThreeSum.LightCoverGreedy.out activePtr rows cols)
          (@List.map.{0, 0} Nat Int (fun (x : Nat) => @Nat.cast.{0} Int instNatCastInt x)
            (ThreeSum.BooleanGreedy.choices matrix rows cols rounds)))
        (And
          (∀ (j : Nat),
            @LT.lt.{0} Nat instLTNat j cols →
              @Eq.{1} Int (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) activePtr j))
                (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BooleanGreedy.active matrix rows cols rounds j)))
          (Light.SameOutside μ μ' activePtr (ThreeSum.LightCoverGreedy.total rows cols rounds)))) := by
  sorry
