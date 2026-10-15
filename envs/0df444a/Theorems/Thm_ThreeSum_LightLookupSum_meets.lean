-- Prove2me | Theorems.Thm_ThreeSum_LightLookupSum_meets
-- name    : ThreeSum.LightLookupSum.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:04:47.46837+00:00
-- url     : https://prove2.me/theorems/6f79fe31-87d5-4ab6-88eb-9020a5eb06c7
-- title:
--   Verified sum of table values selected by keys
-- statement:
--   Let $k,f:\mathbb N\to\mathbb N$, with $k(i)<p$ for $i<n$ and $f(r)\le B$ for $r<p$. Suppose memory $\mu$ stores the $n$ keys at address $K$ and the $p$ table values at address $A$. Assume $K+n,A+p\le\mathrm{space}\le\mathrm{word}$, $nB\le\mathrm{word}$, and the Light program contains the lookup-sum body.
--
--   The call with arguments $(K,A,n,p)$ terminates within $24n+20$ steps and satisfies
--   $$
--   r=\sum_{i=0}^{n-1}f(k(i)),\qquad \nu=\mu.
--   $$
--   This realizes an exact sum of histogram or table entries, retaining repeated keys with their full multiplicity.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLookupSum.lean#L50-L92

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
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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

theorem ThreeSum.LightLookupSum.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pThis : Nat}
  (hThis :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pThis)
      (@Option.some.{0} Light.Stmt ThreeSum.LightLookupSum.body))
  {μ : Nat → Int} {keys table n p B : Nat} (key f : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hkeys : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keys n) lim.space)
  (htable :
    @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) table p) lim.space)
  (hkey :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) keys i))
          (@Nat.cast.{0} Int instNatCastInt (key i)))
  (hrange : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i n → @LT.lt.{0} Nat instLTNat (key i) p)
  (hread :
    ∀ (r : Nat),
      @LT.lt.{0} Nat instLTNat r p →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) table r))
          (@Nat.cast.{0} Int instNatCastInt (f r)))
  (hvalue : ∀ (r : Nat), @LT.lt.{0} Nat instLTNat r p → @LE.le.{0} Nat instLENat (f r) B)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n B))
      lim.word),
  Light.Meets lim P pThis d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt keys)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt table)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p) (@List.nil.{0} Int)))))
    μ (ThreeSum.LightLookupSum.time n) fun (r : Int) (μ' : Nat → Int) =>
    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightLookupSum.prefixSum f key n)))
      (@Eq.{1} (Nat → Int) μ' μ) := by
  sorry
