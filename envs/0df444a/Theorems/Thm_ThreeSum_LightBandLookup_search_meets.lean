-- Prove2me | Theorems.Thm_ThreeSum_LightBandLookup_search_meets
-- name    : ThreeSum.LightBandLookup.search_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:42:29.56612+00:00
-- url     : https://prove2.me/theorems/162b8e46-7869-48cb-ba6a-61a62a82b382
-- title:
--   Correctness and linear step bound for the machine binary lookup
-- statement:
--   Let program $P$ contain the recursive binary-search body at procedure $p$. Let integer memory $\mu$ store $f(i)$ at address $a+i$ for $i<n$, and $2^i$ at address $b+i$ for $i\le W$. For an integer query $x$, assume $K\le n$, $f(i)\le x$ for $i<K$, and $x<f(i)$ for $K\le i<n$.
--
--   Let $S,M,D$ denote the memory, word-magnitude, and call-depth limits. Assume $S\le M$, $a+n\le S$, $b+W+1\le S$, and $n+2^{W+1}+16\le M$. For natural numbers $L,k,d$ satisfying $L\le W$, $k\le K<k+2^L$, and $d+L\le D$, the call at depth $d$ obeys
--
--   $$
--   P_p(a,n,x,b,L,k;\mu)\ \text{returns }K
--   \quad\text{within }120L+30\text{ steps, with final memory }\mu.
--   $$
--
--   This establishes the concrete lookup contract using the stored power table and bounded memory accesses.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandLookup.lean#L35-L126

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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress

theorem ThreeSum.LightBandLookup.search_meets : ∀ {lim : Light.Limits} {P : Light.Program} {pSearch a n powers W : Nat} {x : Int}
  (hprog :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pSearch)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightBandLookup.searchBody pSearch)))
  (μ f : Nat → Int) (K : Nat) (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (ha : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a n) lim.space)
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
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))))
      lim.word)
  (hread :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a i)) (f i))
  (hpowers : ThreeSum.LightSubsetAddress.Powers μ powers W) (hpart : ThreeSum.BinarySearch.Partition f x n K)
  (L k : Nat),
  @LE.le.{0} Nat instLENat L W →
    @LE.le.{0} Nat instLENat k K →
      @LT.lt.{0} Nat instLTNat K
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)) →
        ∀ (d : Nat),
          @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L) lim.depth →
            Light.Meets lim P pSearch d
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                  (@List.cons.{0} Int x
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt powers)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt k) (@List.nil.{0} Int)))))))
              μ (ThreeSum.LightBandLookup.searchTime L) fun (r : Int) (μ' : Nat → Int) =>
              And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt K)) (@Eq.{1} (Nat → Int) μ' μ) := by
  sorry
