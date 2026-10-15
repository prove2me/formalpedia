-- Prove2me | Theorems.Thm_ThreeSum_LightSubsetOffset_meets
-- name    : ThreeSum.LightSubsetOffset.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:05:25.102037+00:00
-- url     : https://prove2.me/theorems/e623bb26-789b-420b-8ea2-acdf2cd37685
-- title:
--   Verified Pascal-table computation of a subset-layer offset
-- statement:
--   Let $L,k,w$ be natural numbers with $L,k\le w$. Suppose integer memory $\mu$ contains the rectangular Pascal table at base $a$: for all $i,j\le w$, $\mu(a+i(w+1)+j)=\binom{i}{j}$. For machine space and word bounds $S,W$, assume $a+(w+1)^2\le S\le W$ and $(w+1)2^{w+1}\le W$. If the called procedure in $P$ is the offset-scan body, execution on $(a,L,k,w)$ at any depth takes at most $30k+20$ steps and returns
--
--   $$
--   r=\operatorname{layerOffset}(L,k)=\sum_{j<k}\binom Lj,\qquad \mu'=\mu.
--   $$
--
--   The offset locates the start of the cardinality-$k$ layer in a compact enumeration ordered by subset size.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSubsetOffset.lean#L27-L81

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
import Theorems.Thm_Light_Ends_for


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

theorem ThreeSum.LightSubsetOffset.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pOffset table W L k : Nat}
  (hprog :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pOffset)
      (@Option.some.{0} Light.Stmt ThreeSum.LightSubsetOffset.body))
  (μ : Nat → Int) (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) table (ThreeSum.LightPascal.tableSize W))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) W
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
      lim.word)
  (htable : ThreeSum.LightPascal.Table μ table W) (hL : @LE.le.{0} Nat instLENat L W)
  (hk : @LE.le.{0} Nat instLENat k W),
  Light.Meets lim P pOffset d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt table)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt k)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt W) (@List.nil.{0} Int)))))
    μ (ThreeSum.LightSubsetOffset.time k) fun (r : Int) (μ' : Nat → Int) =>
    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SubsetAddress.layerOffset L k)))
      (@Eq.{1} (Nat → Int) μ' μ) := by
  sorry
