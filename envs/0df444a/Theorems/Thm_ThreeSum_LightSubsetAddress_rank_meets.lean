-- Prove2me | Theorems.Thm_ThreeSum_LightSubsetAddress_rank_meets
-- name    : ThreeSum.LightSubsetAddress.rank_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:49:38.410322+00:00
-- url     : https://prove2.me/theorems/716c1905-36f3-4738-b060-8032d645411f
-- title:
--   The recursive rank procedure computes compact subset addresses
-- statement:
--   Fix a program containing the recursive rank procedure. Memory $\mu$ stores Pascal coefficients through width $w$ in a rectangular $(w+1)^2$ table at $t$, and powers $2^i$ for $i\le w$ at $p$. For memory and word limits $S,W$, assume $t+(w+1)^2\le S$, $p+w+1\le S$, $S\le W$, and $2^{w+1}\le W$. Let $L\le w$ and let $m<2^L$ have exactly $k$ selected bits. At any depth $d$ with $d+L$ within the depth limit, the call on $(L,k,m,w,t,p)$ returns
--
--   $$r=\operatorname{layerRank}(L,k,m),\qquad\mu'=\mu,\qquad\text{cost}\le100L+30.$$
--
--   This gives an executable compact address calculation with cost linear in mask width.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSubsetAddress.lean#L49-L134

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
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

theorem ThreeSum.LightSubsetAddress.rank_meets : ∀ {lim : Light.Limits} {P : Light.Program} {pRank W table powers : Nat}
  (hprog :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pRank)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightSubsetAddress.rankBody pRank)))
  (μ : Nat → Int) (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (htspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) table (ThreeSum.LightPascal.tableSize W))
      lim.space)
  (hpspace :
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
  (htable : ThreeSum.LightPascal.Table μ table W) (hpowers : ThreeSum.LightSubsetAddress.Powers μ powers W)
  (L k m : Nat),
  @LE.le.{0} Nat instLENat L W →
    ThreeSum.SubsetAddress.IsMask L k m →
      ∀ (d : Nat),
        @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L) lim.depth →
          Light.Meets lim P pRank d
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt k)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt m)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt W)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt table)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt powers) (@List.nil.{0} Int)))))))
            μ (ThreeSum.LightSubsetAddress.rankTime L) fun (r : Int) (μ' : Nat → Int) =>
            And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SubsetAddress.layerRank L k m)))
              (@Eq.{1} (Nat → Int) μ' μ) := by
  sorry
