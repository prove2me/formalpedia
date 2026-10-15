-- Prove2me | Theorems.Thm_ThreeSum_LightSubsetEnumeration_meets
-- name    : ThreeSum.LightSubsetEnumeration.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:37:49.019324+00:00
-- url     : https://prove2.me/theorems/3883f827-9074-485a-bda7-da67aac7824f
-- title:
--   Verified enumeration of a fixed-cardinality mask layer
-- statement:
--   Let $L,k,B,a,z,p,d\in\mathbb N$, where $L$ is the remaining width, $B$ the table width, $a$ the initial offset, $z$ the output base, and $p$ the power-table base. Assume $L\le B$, $k\le B+1$, $a+2^L\le2^B$, $z+\binom Lk\le p$, and memory stores $2^i$ at $p+i$ for $i\le B$. For machine space, word, and depth bounds $S,W,D$, assume $S\le W$, $p+B+1\le S$, $2^{B+1}\le W$, and $d+L\le D$. Suppose the program contains the specified enumeration body at its self-call index. The procedure returns and writes
--
--   $$
--   \mathrm{result}=\binom Lk,\qquad\nu[z:]=[a+m:m\text{ in the canonical width-}L\text{ weight-}k\text{ mask list}].
--   $$
--
--   It runs within the defined budget $150\operatorname{enumerationWork}(L,k)$ and preserves memory outside the $\binom Lk$ output cells. This verifies the concrete layer enumerator, including empty layers.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSubsetEnumeration.lean#L65-L203

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
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightSubsetEnumeration.meets : ∀ {lim : Light.Limits} {P : Light.Program} {pEnum W powers : Nat}
  (hprog :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pEnum)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightSubsetEnumeration.body pEnum)))
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) powers
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      lim.word)
  (L k pref dst : Nat) (μ : Nat → Int),
  @LE.le.{0} Nat instLENat L W →
    @LE.le.{0} Nat instLENat k
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pref
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W) →
        @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst (L.choose k))
            powers →
          ThreeSum.LightSubsetAddress.Powers μ powers W →
            ∀ (d : Nat),
              @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L) lim.depth →
                Light.Meets lim P pEnum d
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt k)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt pref)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt powers) (@List.nil.{0} Int))))))
                  μ (ThreeSum.LightSubsetEnumeration.time L k) fun (r : Int) (μ' : Nat → Int) =>
                  And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (L.choose k)))
                    (And (Light.Seg μ' dst (ThreeSum.LightSubsetEnumeration.output L k pref))
                      (Light.SameOutside μ μ' dst (L.choose k))) := by
  sorry
