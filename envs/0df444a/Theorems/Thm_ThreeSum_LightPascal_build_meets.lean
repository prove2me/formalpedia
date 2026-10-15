-- Prove2me | Theorems.Thm_ThreeSum_LightPascal_build_meets
-- name    : ThreeSum.LightPascal.build_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:45:37.104801+00:00
-- url     : https://prove2.me/theorems/2d71c170-c71c-4134-8d04-0bdc12960ffc
-- title:
--   Constructing a complete Pascal table in bounded memory
-- statement:
--   Let $L$ and the destination address $a$ be natural numbers. Assume the program contains the specified Pascal-table, row, fill, and linear-array procedures. With space, word, and depth limits $S,B,D$, suppose
--   $$a+(L+1)^2\le S\le B,\quad2^{L+1}\le B,\quad d+1<D.$$
--   Starting from any memory, the constructor terminates within $23L^2+139L+119$ steps and produces
--   $$\nu\bigl(a+i(L+1)+j\bigr)=\binom ij\qquad(0\le i,j\le L).$$
--   This includes the zero entries above each row's diagonal. Every address outside the $(L+1)^2$-cell table retains its original value.
--
--   The contract supplies a complete table of exact binomial coefficients for later finite enumeration and indexing routines.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightPascal.lean#L92-L165

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
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Bounds
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
import Theorems.Thm_ThreeSum_LightArray_linear_bounded_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

theorem ThreeSum.LightPascal.build_meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pBuild pFill pRow pLinear : Nat}
  (hbuild :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pBuild)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightPascal.buildBody pFill pRow)))
  (hfill :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pFill)
      (@Option.some.{0} Light.Stmt Light.fillBody))
  (hrow :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pRow)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightPascal.rowBody pLinear)))
  (hlinear :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pLinear)
      (@Option.some.{0} Light.Stmt ThreeSum.LightArray.linearBody))
  {μ : Nat → Int} {dst L : Nat}
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      lim.depth)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst (ThreeSum.LightPascal.tableSize L))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      lim.word),
  Light.Meets lim P pBuild d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L) (@List.nil.{0} Int)))
    μ (ThreeSum.LightPascal.buildTime L) fun (x : Int) (μ' : Nat → Int) =>
    And (ThreeSum.LightPascal.Table μ' dst L) (Light.SameOutside μ μ' dst (ThreeSum.LightPascal.tableSize L)) := by
  sorry
