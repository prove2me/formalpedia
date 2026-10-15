-- Prove2me | Theorems.Thm_ThreeSum_LightNormalize_dedup_meets
-- name    : ThreeSum.LightNormalize.dedup_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:37:40.009169+00:00
-- url     : https://prove2.me/theorems/0ad10a7f-3f9c-4768-8145-dbf602dfaf2c
-- title:
--   Verified linear deduplication of a sorted segment
-- statement:
--   Let $L$ be a nondecreasing integer list of length $n$, stored in memory $\mu$ at base $a$. Let $z$ be an output base with $a+n\le z$ and $z+n\le S$, where $S$ is the machine space bound. Assume $S\le W$, $1\le W$, and $d+n\le D$ for word bound $W$, depth limit $D$, and starting depth $d$. If procedure $p$ in $P$ is the specified recursive deduplicator, it terminates within $200n+30$ steps with
--
--   $$
--   \mathrm{result}=|\operatorname{dedup}(L)|,\qquad\nu[z:]=\operatorname{dedup}(L),\qquad\nu(x)=\mu(x)\ (x\notin[z,z+n)).
--   $$
--
--   The segment equality refers to the output-list length. Deduplication retains the last occurrence of each value, matching the list specification and preserving sorted color-class membership.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightNormalize.lean#L52-L123

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
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Theorems.Thm_Light_seg_cons


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightNormalize.dedup_meets : ∀ {lim : Light.Limits} {P : Light.Program} {pDedup : Nat}
  (hprog :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pDedup)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightNormalize.dedupBody pDedup)))
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (h1 : @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))) lim.word)
  (L : List.{0} Int) (μ : Nat → Int) (src dst d : Nat),
  @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LE.le.{0} Int Int.instLEInt x1 x2) L →
    Light.Seg μ src L →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src (@List.length.{0} Int L)) dst →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst (@List.length.{0} Int L)) lim.space →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d (@List.length.{0} Int L)) lim.depth →
            Light.Meets lim P pDedup d
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int L))
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst) (@List.nil.{0} Int))))
              μ (ThreeSum.LightNormalize.dedupTime (@List.length.{0} Int L)) fun (r : Int) (μ' : Nat → Int) =>
              And
                (@Eq.{1} Int r
                  (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int (@List.dedup.{0} Int Int.instDecidableEq L))))
                (And (Light.Seg μ' dst (@List.dedup.{0} Int Int.instDecidableEq L))
                  (Light.SameOutside μ μ' dst (@List.length.{0} Int L))) := by
  sorry
