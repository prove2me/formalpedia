-- Prove2me | Theorems.Thm_ThreeSum_LightBandTable_row_meets
-- name    : ThreeSum.LightBandTable.row_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:20:34.52297+00:00
-- url     : https://prove2.me/theorems/0a94869c-fe23-4e31-9bdd-a319e321f9d3
-- title:
--   The band-table row procedure writes the exact interval-lookup results
-- statement:
--   Suppose a program contains the specified row, interval-lookup, and recursive binary-search procedures. Memory $\mu$ stores $n$ integers $f_j$ at $b$, $m$ lower and upper endpoints at $\ell,u$, and powers $2^i$ for $i\le W$ at $v$. Assume the lower endpoints are nondecreasing, $m<2^W$, $|s|\le1$, and $|x|,|f_j|\le U$. For space, word, and depth limits $S,M,D$, require
--   $$\begin{gathered}S\le M,\quad b+n,\ell+m,u+m\le z,\quad z+n\le v,\quad v+W+1\le S,\\m+2^{W+1}+16\le M,\quad2U\le M,\quad d+W+2\le D.\end{gathered}$$
--   Let $R(y)$ be the index plus one of the last lower endpoint at most $y$, provided its upper endpoint is at least $y$; otherwise let $R(y)=0$. The row call with $(x,b,\ell,u,n,m,z,v,W,s)$ finishes within $n(120W+190)+6$ steps and satisfies
--   $$\mu'(z+j)=R(sx+f_j)\quad(j<n),\qquad \mu'|_{\mathbb N\setminus[z,z+n)}=\mu|_{\mathbb N\setminus[z,z+n)}.$$
--
--   This certifies each physical row of the band-owner lookup table.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandTable.lean#L31-L105

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
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
import Theorems.Thm_ThreeSum_LightBandLookup_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress

theorem ThreeSum.LightBandTable.row_meets : ∀ {lim : Light.Limits} {P : Light.Program} {pRow pLookup pSearch b loBase hiBase n m dst powers W d U : Nat} {x s : Int}
  (hrow :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pRow)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightBandTable.rowBody pLookup)))
  (hlookup :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pLookup)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightBandLookup.body pSearch)))
  (hsearch :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pSearch)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightBandLookup.searchBody pSearch)))
  (μ f lo hi : Nat → Int) (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hb : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b n) dst)
  (hlo : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) loBase m) dst)
  (hhi : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hiBase m) dst)
  (hdst : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst n) powers)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) powers
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))))
      lim.word)
  (hqueryWord :
    @LE.le.{0} Int Int.instLEInt
      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) (@Nat.cast.{0} Int instNatCastInt U))
      lim.word)
  (hread :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b j)) (f j))
  (hreadLo :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j m →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) loBase j)) (lo j))
  (hreadHi :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j m →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) hiBase j)) (hi j))
  (hpowers : ThreeSum.LightSubsetAddress.Powers μ powers W)
  (hsorted :
    ∀ (i j : Nat),
      @LE.le.{0} Nat instLENat i j → @LT.lt.{0} Nat instLTNat j m → @LE.le.{0} Int Int.instLEInt (lo i) (lo j))
  (hm :
    @LT.lt.{0} Nat instLTNat m
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W))
  (hs :
    @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup s)
      (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
  (hx :
    @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup x) (@Nat.cast.{0} Int instNatCastInt U))
  (hf :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j n →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (f j))
          (@Nat.cast.{0} Int instNatCastInt U))
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d W)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      lim.depth),
  Light.Meets lim P pRow d
    (@List.cons.{0} Int x
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt loBase)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt hiBase)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt m)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt powers)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt W)
                      (@List.cons.{0} Int s (@List.nil.{0} Int)))))))))))
    μ (ThreeSum.LightBandTable.rowTime n W) fun (x_1 : Int) (μ' : Nat → Int) =>
    And
      (∀ (j : Nat),
        @LT.lt.{0} Nat instLTNat j n →
          @Eq.{1} Int (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst j))
            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBandTable.rowValue lo hi m x s f j)))
      (Light.SameOutside μ μ' dst n) := by
  sorry
