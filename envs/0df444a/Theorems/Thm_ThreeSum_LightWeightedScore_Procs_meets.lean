-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedScore_Procs_meets
-- name    : ThreeSum.LightWeightedScore.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:40:31.444231+00:00
-- url     : https://prove2.me/theorems/44807b3e-3e0d-4ea0-bf93-8f429a3aac1e
-- title:
--   Execute the weighted modular score on original integer arrays
-- statement:
--   Let arrays $A,B,C$ have lengths at most $N$ and entry magnitudes at most $U$. Let $q>0$ and let $\ell_0,\ldots,\ell_{s-1}$ be distinct primes with $q\le M$ and $q\ell_i\le M$. All arrays and the prime list are stored below scratch $f$. Write $C(t)$ for the count of original triples satisfying $t\mid C_k-B_j-A_i$, and put $j_i=q$ if $\ell_i\mid q$, otherwise $j_i=q\ell_i$.
--
--   Assume the specified counting and joint-modulus procedures, their weighted-score space and word budgets, $S\le W$, and $d+\lceil\log_2M\rceil+4\le D$. The routine returns
--   $$r=sC(q)-\sum_{i<s}C(j_i).$$
--   It preserves memory below $f$. If $T_c$ is the modular-count budget at $M$ and $R_M$ its remainder budget, execution takes at most $T_c+s(T_c+R_M+140)+100$ steps.
--
--   This certifies the weighted score with all modular counts computed from the original signed arrays.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightWeightedScore.lean#L233-L298

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
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
import Theorems.Thm_ThreeSum_LightModuloCounts_meets
import Theorems.Thm_ThreeSum_LightWeightedScore_meets_of_count_backend


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.Arithmetic
end ThreeSum.Arithmetic
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightModuloCounts
end ThreeSum.LightModuloCounts
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

theorem ThreeSum.LightWeightedScore.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (C : ThreeSum.LightWeightedScore.Procs P pMain)
  {μ : Nat → Int} {a b c nA nB nC q N aux s free maxMod U : Nat} (primes : Nat → Nat)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q)
  (hqmax : @LE.le.{0} Nat instLENat q maxMod)
  (ha : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a nA) free)
  (hb : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b nB) free)
  (hc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c nC) free)
  (haux : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) aux s) free)
  (hnA : @LE.le.{0} Nat instLENat nA N) (hnB : @LE.le.{0} Nat instLENat nB N) (hnC : @LE.le.{0} Nat instLENat nC N)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightWeightedScore.space free maxMod N U) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightWeightedScore.word maxMod N s U))
      lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (Nat.clog (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) maxMod))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      lim.depth)
  (hA :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i nA →
        @LE.le.{0} Int Int.instLEInt
          (@abs.{0} Int instLatticeInt Int.instAddGroup
            (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a i)))
          (@Nat.cast.{0} Int instNatCastInt U))
  (hB :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i nB →
        @LE.le.{0} Int Int.instLEInt
          (@abs.{0} Int instLatticeInt Int.instAddGroup
            (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b i)))
          (@Nat.cast.{0} Int instNatCastInt U))
  (hC :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i nC →
        @LE.le.{0} Int Int.instLEInt
          (@abs.{0} Int instLatticeInt Int.instAddGroup
            (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c i)))
          (@Nat.cast.{0} Int instNatCastInt U))
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
        @LE.le.{0} Nat instLENat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q (primes i)) maxMod),
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
    μ (ThreeSum.LightWeightedScore.runtimeTime maxMod nA nB nC s U) fun (r : Int) (μ' : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt
          (ThreeSum.WeightedScore.score primes s q nA nB nC
            (fun (j : Nat) => μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a j))
            (fun (j : Nat) => μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b j)) fun (j : Nat) =>
            μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c j))))
      (Light.Kept μ μ' free) := by
  sorry
