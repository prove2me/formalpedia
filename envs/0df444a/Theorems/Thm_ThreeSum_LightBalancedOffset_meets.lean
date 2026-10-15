-- Prove2me | Theorems.Thm_ThreeSum_LightBalancedOffset_meets
-- name    : ThreeSum.LightBalancedOffset.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:37:36.968986+00:00
-- url     : https://prove2.me/theorems/7bd56588-3970-4baf-8c2c-614432a7ab6c
-- title:
--   Compute the least offset minimizing cyclic histogram correlation
-- statement:
--   Let $p>0$, $p\le2^k$, and let $F,H:\mathbb Z/p\mathbb Z\to\mathbb N$ have coefficients at most $U$. Memory stores their length-$2^k$ padded arrays, with the second array representing $z\mapsto H(-z)$. Reserve a $2^{k+1}$-cell product buffer and a disjoint $p$-cell correlation buffer; these and both inputs end below scratch $f$. Assume the specified cyclic product and minimum procedures, $f+8\cdot2^k\le S\le W$, $128(2^k)^3(U+1)^2\le W$, and $d+k+3\le D$.
--
--   Writing $C(r)=\sum_zF(z)H(z-r)$, the routine returns
--   $$r=\min\operatorname*{arg\,min}_{0\le t<p}C(t).$$
--   Its time is the defined cyclic-convolution budget plus $32p+120$. Memory below $f$ outside the product and correlation buffers is preserved.
--
--   This gives a deterministic, tie-resolving choice of a balanced cyclic offset.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBalancedOffset.lean#L45-L77

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
import Definitions.Def_ThreeSum1962Source_Bundle07
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
import Theorems.Thm_ThreeSum_LightCyclic_correlation_meets
import Theorems.Thm_ThreeSum_LightMinimum_meets


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

theorem ThreeSum.LightBalancedOffset.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain pCyclic pMinimum pMultiply pHalf pLinear pFill : Nat}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightBalancedOffset.body pCyclic pMinimum)))
  (hcyclic :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pCyclic)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightCyclic.body pMultiply pLinear)))
  (hminimum :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMinimum)
      (@Option.some.{0} Light.Stmt ThreeSum.LightMinimum.body))
  (K : ThreeSum.LightKaratsuba.Procs P pMultiply pHalf pLinear pFill) {μ : Nat → Int} {k a b prod dst work p U : Nat}
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
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      lim.depth),
  Light.Meets lim P pMain d
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
    μ (ThreeSum.LightBalancedOffset.time k p) fun (r : Int) (μ' : Nat → Int) =>
    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (@ThreeSum.LightBalancedOffset.offset p inst F H)))
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
