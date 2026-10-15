-- Prove2me | Theorems.Thm_ThreeSum_LightMaskErase_meets
-- name    : ThreeSum.LightMaskErase.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:53:00.165592+00:00
-- url     : https://prove2.me/theorems/79815ac9-134f-44fd-a7d6-bee17af14e13
-- title:
--   The executable mask eraser clears one bit within a linear time budget
-- statement:
--   Let a program contain the recursive mask-erasing procedure at $p_E$, with space, word, and depth limits $S,M,D$. Suppose memory $\mu$ stores $2^j$ at $u+j$ for $j\le W$, and assume
--   $$S\le M,\qquad u+W+1\le S,\qquad 2^{W+1}\le M.$$
--   For natural numbers $L,a,m,d$ satisfying $L\le W$, $a\le W$, $m<2^L$, and $d+L\le D$, the call with arguments $(L,a,m,W,u)$ succeeds within $100L+30$ steps and returns
--   $$r=m-2^a\operatorname{bit}_a(m),\qquad \mu'=\mu.$$
--   Thus it clears coordinate $a$ while keeping the other bit positions fixed; for $a\ge L$, the mask is unchanged.
--
--   This certifies the bit-removal operation used by subsequent subset and hash computations.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightMaskErase.lean#L32-L99

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
import Definitions.Def_ThreeSum1962Source_Bundle03
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
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase

theorem ThreeSum.LightMaskErase.meets : ∀ {lim : Light.Limits} {P : Light.Program} {pErase W powers : Nat}
  (hprog :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pErase)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightMaskErase.body pErase)))
  (μ : Nat → Int) (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
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
  (hpowers : ThreeSum.LightSubsetAddress.Powers μ powers W) (L a m : Nat),
  @LE.le.{0} Nat instLENat L W →
    @LE.le.{0} Nat instLENat a W →
      @LT.lt.{0} Nat instLTNat m
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L) →
        ∀ (d : Nat),
          @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d L) lim.depth →
            Light.Meets lim P pErase d
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt L)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt m)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt W)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt powers) (@List.nil.{0} Int))))))
              μ (ThreeSum.LightMaskErase.time L) fun (r : Int) (μ' : Nat → Int) =>
              And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (ThreeSum.MaskErase.eraseMask L a m)))
                (@Eq.{1} (Nat → Int) μ' μ) := by
  sorry
