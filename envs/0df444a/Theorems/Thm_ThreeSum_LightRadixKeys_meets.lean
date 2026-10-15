-- Prove2me | Theorems.Thm_ThreeSum_LightRadixKeys_meets
-- name    : ThreeSum.LightRadixKeys.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:46:55.72932+00:00
-- url     : https://prove2.me/theorems/97931634-73c5-4051-8c5b-06c1d28d7b82
-- title:
--   Constructing all radix-product keys with occurrence multiplicity
-- statement:
--   Let $X$ be a nonempty integer list of length $m$, with $|x|\le U$, stored at $s$. Fix a natural radix $p$. Define $V_0=[0]$ and $V_{j+1}$ by concatenating, in $X$ order, the lists $[x+py:y\in V_j]$. Put $o_j=\sum_{i<j}(1+m^i)$. Assume the specified recursive constructor, row constructor, and affine procedure are present, and
--   $$s+m\le a,\quad a+o_J+1+m^J\le S\le B,\quad U+pU(p+1)^J+p+1\le B,\quad d+J+2\le D.$$
--   The constructor returns $H=a+o_J$ and writes
--   $$\nu(H)=m^J,\qquad \nu(H+1+i)=(V_J)_i\quad(i<m^J).$$
--   Cells below $a$ are preserved. Its budget is $T_0=50$, $T_{j+1}=T_j+m(23m^j+106)+220$.
--
--   The output retains every product occurrence, including repeated integer keys.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightRadixKeys.lean#L97-L199

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
import Definitions.Def_ThreeSum1962Source_Bundle07
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
import Theorems.Thm_Light_seg_cons
import Theorems.Thm_ThreeSum_LightRadixRows_meets
import Theorems.Thm_ThreeSum_RadixKeyLists_values_bounded


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightRadixKeys.meets : ∀ {lim : Light.Limits} {P : Light.Program} {pMain pRows pAffine src dst p U : Nat}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightRadixKeys.body pMain pRows)))
  (hrows :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pRows)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightRadixRows.body pAffine)))
  (haffine :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pAffine)
      (@Option.some.{0} Light.Stmt ThreeSum.LightReportingAffine.body))
  (base : List.{0} Int) (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hsrc :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src (@List.length.{0} Int base)) dst)
  (hm :
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.length.{0} Int base))
  (hbound :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) base x →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup x)
          (@Nat.cast.{0} Int instNatCastInt U))
  (J d : Nat) (μ : Nat → Int),
  @LE.le.{0} Nat instLENat (ThreeSum.LightRadixKeys.space dst (@List.length.{0} Int base) J) lim.space →
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightRadixKeys.word p U J)) lim.word →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d J)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          lim.depth →
        Light.Seg μ src base →
          Light.Meets lim P pMain d
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int base))
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst) (@List.nil.{0} Int))))))
            μ (ThreeSum.LightRadixKeys.time (@List.length.{0} Int base) J) fun (r : Int) (ν : Nat → Int) =>
            And
              (@Eq.{1} Int r
                (@Nat.cast.{0} Int instNatCastInt
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                    (ThreeSum.LightRadixKeys.offset (@List.length.{0} Int base) J))))
              (And
                (@Eq.{1} Int
                  (ν
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                      (ThreeSum.LightRadixKeys.offset (@List.length.{0} Int base) J)))
                  (@Nat.cast.{0} Int instNatCastInt
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@List.length.{0} Int base) J)))
                (And
                  (Light.Seg ν
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
                        (ThreeSum.LightRadixKeys.offset (@List.length.{0} Int base) J))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (ThreeSum.RadixKeyLists.values (@Nat.cast.{0} Int instNatCastInt p) base J))
                  (Light.Kept μ ν dst))) := by
  sorry
