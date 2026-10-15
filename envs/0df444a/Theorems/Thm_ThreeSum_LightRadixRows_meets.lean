-- Prove2me | Theorems.Thm_ThreeSum_LightRadixRows_meets
-- name    : ThreeSum.LightRadixRows.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:33:14.194468+00:00
-- url     : https://prove2.me/theorems/addbda2c-9ec9-403f-bc62-0d88f78d4e1e
-- title:
--   Constructing all ordered radix-extension rows
-- statement:
--   Let integer lists $X,Y$, of lengths $m,n$, be stored at $A,B$, and let $p,U,V\in\mathbb N$. Suppose $|x|\le U$ for $x\in X$, $|y|\le V$ for $y\in Y$, $A+m,B+n\le D$, and $D+mn\le\mathrm{space}\le\mathrm{word}$. Require $U+pV+p+1\le\mathrm{word}$, current depth below the call-depth limit, and the radix-row and affine-scan bodies in the program.
--
--   The call with $(A,B,D,m,n,p)$ terminates within $m(23n+106)+20$ steps, writes the ordered list
--   $$
--   [x+py\mid x\in X\text{ in list order},\ y\in Y\text{ in list order}]
--   $$
--   at $D$, and preserves memory outside $[D,D+mn)$.
--
--   This constructs the full positional-key product while retaining repetitions and their original order.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightRadixRows.lean#L36-L119

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_Light_Ends_pass
import Theorems.Thm_Light_seg_append


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightArray
end ThreeSum.LightArray
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightRadixRows.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain pAffine srcBase srcPrev dst p U V : Nat} {μ : Nat → Int}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightRadixRows.body pAffine)))
  (haffine :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pAffine)
      (@Option.some.{0} Light.Stmt ThreeSum.LightReportingAffine.body))
  (base prev : List.{0} Int) (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hbaseEnd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcBase (@List.length.{0} Int base)) dst)
  (hprevEnd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcPrev (@List.length.{0} Int prev)) dst)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@List.length.{0} Int base)
          (@List.length.{0} Int prev)))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightRadixRows.word p U V)) lim.word)
  (hd : @LT.lt.{0} Nat instLTNat d lim.depth) (hbaseRead : Light.Seg μ srcBase base)
  (hprevRead : Light.Seg μ srcPrev prev)
  (hbaseBound :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) base x →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup x)
          (@Nat.cast.{0} Int instNatCastInt U))
  (hprevBound :
    ∀ (y : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) prev y →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup y)
          (@Nat.cast.{0} Int instNatCastInt V)),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcBase)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcPrev)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int base))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int prev))
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p) (@List.nil.{0} Int)))))))
    μ (ThreeSum.LightRadixRows.time (@List.length.{0} Int base) (@List.length.{0} Int prev))
    fun (x : Int) (ν : Nat → Int) =>
    And (Light.Seg ν dst (ThreeSum.RadixKeyLists.step (@Nat.cast.{0} Int instNatCastInt p) base prev))
      (Light.SameOutside μ ν dst
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@List.length.{0} Int base)
          (@List.length.{0} Int prev))) := by
  sorry
