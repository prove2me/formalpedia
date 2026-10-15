-- Prove2me | Theorems.Thm_ThreeSum_LightEncodedColorPrimeCore_program_meets
-- name    : ThreeSum.LightEncodedColorPrimeCore.program_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:59:09.781658+00:00
-- url     : https://prove2.me/theorems/d2005dbb-e512-4f34-89d8-cd805d656541
-- title:
--   Constructing a prime pool and retaining the complete common-modulus chain
-- statement:
--   Write $S,\Omega,\Delta$ for machine space, word magnitude, and depth limits. Let three stored integer arrays, bounded by $U$, have lengths $n_A,n_B,n_C$. Let $g,y>0$ and let $\mathcal R$ contain Boolean-flagged band records with valid starts for flagged records. Fix a natural target scale $M$, and let $L$ be the integer logarithm of $\lfloor M/4\rfloor$ to base $4y$, with the natural-number convention at zero. Enumerate the primes $y<p\le4y$ in increasing order. Starting with $Q_0=1$, form $Q_{j+1}$ by multiplying $Q_j$ by the first prime minimizing the aggregate weighted false score.
--
--   Assume the inputs end before $f$, $(4y)^{L+1}\le M_{\max}$, the core space and word bounds, $S\le\Omega$, and $d+\lceil\log_2 M_{\max}\rceil+9\le\Delta$. The routine returns $Q_L$ and retains the prime pool and every $Q_j$ for $j\le L$, with header
--   $$[Q_L,L,f_{\rm next},f+6,s,f+6+3y],\qquad
--   f_{\rm next}=f+6+3y+L+1,$$
--   where $s$ is the pool size. Cells below $f$ are preserved within the stated core time.
--
--   This packages the common-modulus construction as retained machine data.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightEncodedColorPrimeCore.lean#L55-L171

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_LightBandPrimeChain_program_meets
import Theorems.Thm_ThreeSum_LightBandPrimeDepth_meets
import Theorems.Thm_ThreeSum_LightPrimePool_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimePool_prefix_increasing


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPrimeChoice
end ThreeSum.BandPrimeChoice
namespace ThreeSum.BandWeightedScore
end ThreeSum.BandWeightedScore
namespace ThreeSum.EncodedColorPrimeData
end ThreeSum.EncodedColorPrimeData
namespace ThreeSum.WeightedScore
end ThreeSum.WeightedScore
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightEncodedColorPrimeCore.program_meets : ∀ {lim : Light.Limits} {d : Nat} {μ : Nat → Int} {a b c nA nB nC g recs M y free maxMod U : Nat}
  (rs : List.{0} ThreeSum.BandCandidateRows.Record)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hy : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) y)
  (hg : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g)
  (ha : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a nA) free)
  (hb : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b nB) free)
  (hc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c nC) free)
  (hrecs :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) recs
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@List.length.{0} ThreeSum.BandCandidateRows.Record rs)))
      free)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightEncodedColorPrimeCore.space free maxMod g M y U) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (ThreeSum.LightEncodedColorPrimeCore.word maxMod nA nB nC g
          (@List.length.{0} ThreeSum.BandCandidateRows.Record rs) M y U))
      lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (Nat.clog (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) maxMod))
        (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
      lim.depth)
  (hrecords : Light.Seg μ recs (ThreeSum.BandCandidateRows.cells rs))
  (hflag :
    ∀ (r : ThreeSum.BandCandidateRows.Record),
      @Membership.mem.{0, 0} ThreeSum.BandCandidateRows.Record (List.{0} ThreeSum.BandCandidateRows.Record)
          (@List.instMembership.{0} ThreeSum.BandCandidateRows.Record) rs r →
        Or (@Eq.{1} Nat r.flag (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Eq.{1} Nat r.flag (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (hvalid :
    ∀ (r : ThreeSum.BandCandidateRows.Record),
      @Membership.mem.{0, 0} ThreeSum.BandCandidateRows.Record (List.{0} ThreeSum.BandCandidateRows.Record)
          (@List.instMembership.{0} ThreeSum.BandCandidateRows.Record) rs r →
        @Eq.{1} Nat r.flag (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          And (@LE.le.{0} Nat instLENat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r.a g) nA)
            (And (@LE.le.{0} Nat instLENat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r.b g) nB)
              (@LE.le.{0} Nat instLENat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) r.c g) nC)))
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
  (hmax :
    @LE.le.{0} Nat instLENat
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) y)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LightBandPrimeDepth.depth M y)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      maxMod),
  Light.Meets lim ThreeSum.LightEncodedColorPrimeCore.program
    (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt c)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nA)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nB)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nC)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt g)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt recs)
                    (@List.cons.{0} Int
                      (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} ThreeSum.BandCandidateRows.Record rs))
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt M)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt y)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free) (@List.nil.{0} Int)))))))))))))
    μ (ThreeSum.LightEncodedColorPrimeCore.time maxMod g (@List.length.{0} ThreeSum.BandCandidateRows.Record rs) M y U)
    fun (result : Int) (ν : Nat → Int) =>
    And
      (@Eq.{1} Int result
        (@Nat.cast.{0} Int instNatCastInt
          (ThreeSum.LightBandPrimeConstruction.modulus y nA nB nC g
            (fun (j : Nat) => μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a j))
            (fun (j : Nat) => μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b j))
            (fun (j : Nat) => μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c j)) rs
            (ThreeSum.LightBandPrimeDepth.depth M y))))
      (And
        (ThreeSum.EncodedColorPrimeData.Stored ν free M y
          (ThreeSum.LightBandPrimeConstruction.modulus y nA nB nC g
            (fun (j : Nat) => μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a j))
            (fun (j : Nat) => μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b j))
            (fun (j : Nat) => μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c j)) rs))
        (Light.Kept μ ν free)) := by
  sorry
