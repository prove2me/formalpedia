-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedScore_meets_of_count_backend
-- name    : ThreeSum.LightWeightedScore.meets_of_count_backend
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:37:30.73675+00:00
-- url     : https://prove2.me/theorems/194a9817-12b0-4059-bf4c-7f876c6a3492
-- title:
--   Verified weighted-score loop given an exact modular-counting backend
-- statement:
--   Let integer arrays $A,B,C$ of lengths $n_A,n_B,n_C\le N\le S$ and an array of $s$ distinct primes $p_i$ be stored wholly below free address $f$. Let $0<q\le M$ and $qp_i\le M$. Assume $S\le W$, $f+\lfloor\log_2(M+1)\rfloor+2\le S$, $(s+1)N^3+8M+16\le W$, and $d+1<D$. Suppose $P$ contains the weighted-score and joint-modulus bodies, the Euclidean-remainder helper, and a backend which, for every $0<v\le M$ and every memory agreeing with the initial memory below $f$, counts all triples with $v\mid C_k-B_j-A_i$ within $T_c$ steps at depth $d+1$, preserving that prefix. The score procedure returns
--
--   $$
--   r=\sum_{i<n_A,j<n_B,k<n_C}\mathbf1_{q\mid\Delta_{ijk}}
--   |\{u<s:p_u\nmid\Delta_{ijk}\}|,
--   \quad\Delta_{ijk}=C_k-B_j-A_i.
--   $$
--
--   It preserves memory below $f$ and takes at most $T_c+s(T_c+R_M+140)+100$ steps, where $R_M=43(\lfloor\log_2(M+1)\rfloor+1)+34$.
--
--   This composes exact counting calls into the auxiliary-prime score.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightWeightedScore.lean#L104-L209

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
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Nat
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_Light_emod_meets
import Theorems.Thm_ThreeSum_WeightedScore_score_eq_remaining


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.Arithmetic
end ThreeSum.Arithmetic
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.ModuloCounts
end ThreeSum.ModuloCounts
namespace ThreeSum.WeightedModuli
end ThreeSum.WeightedModuli
namespace ThreeSum.WeightedScore
end ThreeSum.WeightedScore

theorem ThreeSum.LightWeightedScore.meets_of_count_backend : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain pCount pJoint pEmod : Nat}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightWeightedScore.body pCount pJoint)))
  (hjoint :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pJoint)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightWeightedScore.jointBody pEmod)))
  (hem :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pEmod)
      (@Option.some.{0} Light.Stmt Light.emodBody))
  {μ : Nat → Int} {a b c nA nB nC q N aux s free maxMod countTime : Nat} (primes : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      lim.depth)
  (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q)
  (hqmax : @LE.le.{0} Nat instLENat q maxMod)
  (ha : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a nA) free)
  (hb : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b nB) free)
  (hc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c nC) free)
  (haux : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) aux s) free)
  (hN : @LE.le.{0} Nat instLENat N lim.space) (hnA : @LE.le.{0} Nat instLENat nA N)
  (hnB : @LE.le.{0} Nat instLENat nB N) (hnC : @LE.le.{0} Nat instLENat nC N)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (Nat.log (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maxMod
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) s
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) N
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) maxMod))
          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))))
      lim.word)
  (hread :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i s →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) aux i))
          (@Nat.cast.{0} Int instNatCastInt (primes i)))
  (hprime : ∀ (i : Nat), @LT.lt.{0} Nat instLTNat i s → Nat.Prime (primes i))
  (hinj :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i s →
        ∀ (j : Nat), @LT.lt.{0} Nat instLTNat j s → @Eq.{1} Nat (primes i) (primes j) → @Eq.{1} Nat i j)
  (hproduct :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i s →
        @LE.le.{0} Nat instLENat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q (primes i)) maxMod)
  (hcount :
    ∀ (ν : Nat → Int) (p : Nat),
      Light.Kept μ ν free →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p →
          @LE.le.{0} Nat instLENat p maxMod →
            Light.Meets lim P pCount
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt c)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nA)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nB)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nC)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt N)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free) (@List.nil.{0} Int))))))))))
              ν countTime fun (r : Int) (ν' : Nat → Int) =>
              And
                (@Eq.{1} Int r
                  (@Nat.cast.{0} Int instNatCastInt
                    (ThreeSum.ModuloCounts.count p nA nB nC
                      (fun (j : Nat) => μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a j))
                      (fun (j : Nat) => μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b j))
                      fun (j : Nat) => μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c j))))
                (Light.Kept ν ν' free)),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt c)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nA)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nB)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nC)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt q)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt N)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt aux)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt s)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free) (@List.nil.{0} Int))))))))))))
    μ (ThreeSum.LightWeightedScore.time countTime s maxMod) fun (r : Int) (μ' : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt
          (ThreeSum.WeightedScore.score primes s q nA nB nC
            (fun (j : Nat) => μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a j))
            (fun (j : Nat) => μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b j)) fun (j : Nat) =>
            μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c j))))
      (Light.Kept μ μ' free) := by
  sorry
