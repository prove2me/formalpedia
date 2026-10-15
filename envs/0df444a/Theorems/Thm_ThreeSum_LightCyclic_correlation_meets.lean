-- Prove2me | Theorems.Thm_ThreeSum_LightCyclic_correlation_meets
-- name    : ThreeSum.LightCyclic.correlation_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:33:00.72483+00:00
-- url     : https://prove2.me/theorems/2377f0db-024d-4cd8-82ae-31467efbb491
-- title:
--   Computing cyclic correlation by multiplication and folding
-- statement:
--   Let $p>0$, $n=2^k\ge p$, and $F,H:\mathbb Z/p\mathbb Z\to\mathbb N$ have values at most $U$. Memory contains their length-$n$ zero-padded vectors, with the second vector indexed as $H(-x)$. Let product base $q$, result base $a$, and scratch base $w$ satisfy: both input segments, the $2n$-cell product, and the $p$-cell result end before $w$, and product and result intervals are disjoint.
--
--   Assume the specified Karatsuba and linear-array procedures,
--   $$w+8n\le S\le W,\quad128n^3(U+1)^2\le W,\quad d+k+2\le D.$$
--   The correlation routine writes
--   $$\nu(a+r)=\sum_{x\in\mathbb Z/p\mathbb Z}F(x)H(x-r)\qquad(0\le r<p)$$
--   within $T_k+23p+106$ steps, where $T_k$ is the Karatsuba budget. Every cell below $w$ outside the product and result intervals is preserved.
--
--   This implements exact cyclic correlation, including multiplicities in the input histograms.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightCyclic.lean#L86-L128

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_CyclicFold_cyclic_correlation
import Theorems.Thm_ThreeSum_Karatsuba_product_coeff_bound
import Theorems.Thm_ThreeSum_LightArray_linear_bounded_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba

theorem ThreeSum.LightCyclic.correlation_meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pThis pMultiply pHalf pLinear pFill : Nat}
  (hThis :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pThis)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightCyclic.body pMultiply pLinear)))
  (C : ThreeSum.LightKaratsuba.Procs P pMultiply pHalf pLinear pFill) {μ : Nat → Int} {k a b prod dst work p U : Nat}
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) p] (F H : ZMod p → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hpn :
    @LE.le.{0} Nat instLENat p
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
  (hAseg :
    Light.Seg μ a
      (ThreeSum.CyclicFold.padTo
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
        (ThreeSum.CyclicFold.vector p F)))
  (hBseg :
    Light.Seg μ b
      (ThreeSum.CyclicFold.padTo
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
        (ThreeSum.CyclicFold.vector p fun (z : ZMod p) =>
          H
            (@Neg.neg.{0} (ZMod p)
              (@NegZeroClass.toNeg.{0} (ZMod p)
                (@SubNegZeroMonoid.toNegZeroClass.{0} (ZMod p)
                  (@SubtractionMonoid.toSubNegZeroMonoid.{0} (ZMod p)
                    (@SubtractionCommMonoid.toSubtractionMonoid.{0} (ZMod p)
                      (@AddCommGroup.toDivisionAddCommMonoid.{0} (ZMod p)
                        (@Ring.toAddCommGroup.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p))))))))
              z))))
  (hA : ThreeSum.Karatsuba.CoeffBound (ThreeSum.CyclicFold.vector p F) (@Nat.cast.{0} Int instNatCastInt U))
  (hB :
    ThreeSum.Karatsuba.CoeffBound
      (ThreeSum.CyclicFold.vector p fun (z : ZMod p) =>
        H
          (@Neg.neg.{0} (ZMod p)
            (@NegZeroClass.toNeg.{0} (ZMod p)
              (@SubNegZeroMonoid.toNegZeroClass.{0} (ZMod p)
                (@SubtractionMonoid.toSubNegZeroMonoid.{0} (ZMod p)
                  (@SubtractionCommMonoid.toSubtractionMonoid.{0} (ZMod p)
                    (@AddCommGroup.toDivisionAddCommMonoid.{0} (ZMod p)
                      (@Ring.toAddCommGroup.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p))))))))
            z))
      (@Nat.cast.{0} Int instNatCastInt U))
  (haf :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
      work)
  (hbf :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
      work)
  (hpf :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) prod
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)))
      work)
  (hdf : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst p) work)
  (hsep :
    Light.Apart prod
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
      dst p)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) work
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (ThreeSum.LightKaratsuba.wordBound
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
          U))
      lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d k)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      lim.depth),
  Light.Meets lim P pThis d
    (@List.cons.{0} Int
      (@HPow.hPow.{0, 0, 0} Int Nat Int
        (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) k)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt prod)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt work)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p) (@List.nil.{0} Int))))))))
    μ (ThreeSum.LightCyclic.combinedTime k p) fun (x : Int) (μ' : Nat → Int) =>
    And
      (∀ (r : Nat),
        @LT.lt.{0} Nat instLTNat r p →
          @Eq.{1} Int (μ' (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst r))
            (@Nat.cast.{0} Int instNatCastInt
              (@ThreeSum.Balancing.correlation.{0} (ZMod p)
                (@Ring.toAddCommGroup.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))
                (@ZMod.fintype p inst) F H
                (@Nat.cast.{0} (ZMod p)
                  (@AddMonoidWithOne.toNatCast.{0} (ZMod p)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod p)
                      (@Ring.toAddGroupWithOne.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))
                  r))))
      (∀ (j : Nat),
        @LT.lt.{0} Nat instLTNat j work →
          Or (@LT.lt.{0} Nat instLTNat j prod)
              (@LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) prod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)))
                j) →
            Or (@LT.lt.{0} Nat instLTNat j dst)
                (@LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst p) j) →
              @Eq.{1} Int (μ' j) (μ j)) := by
  sorry
