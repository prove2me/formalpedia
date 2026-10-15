-- Prove2me | Theorems.Thm_ThreeSum_LightReportingWantedScan_program_meets
-- name    : ThreeSum.LightReportingWantedScan.program_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:28:48.867577+00:00
-- url     : https://prove2.me/theorems/95950688-d090-48de-b88f-a96bc4ca28ad
-- title:
--   The ascending wanted scan returns the first accepted prefix within its cost sum
-- statement:
--   Let $n,N,D,d,\tau\in\mathbb N$, with $\tau$ the acceptance threshold. Let $C$ fix the dispatcher controls, counter address $q$, and layout boundary $\ell$. Let $m_i,t_i\in\mathbb N$ be per-slot masses and time bounds, $H(i)$ a hit predicate, and $I$ a memory invariant. Put $M_j=\sum_{i<j}m_i$. Start with $I(\mu)$ and $\mu(q)=0$. For each $i<N$, every invariant memory with counter $M_i$, and each depth $e$ with $e+i\le D+1$, assume dispatcher procedure $151$ finishes within $t_i$, returns a bit testing $\tau<M_{i+1}$ or $H(i)$, sets the counter to $M_{i+1}$, preserves $I$, and preserves memory below $\ell$ except at $q$.
--
--   Assume $n\le N$, $d+n\le D$, and machine limits satisfying $N+1\le\mathrm{space}\le\mathrm{word}$ and $D+1\le\mathrm{depth}$. The scan at depth $d$ returns a bit $r$ in a number of steps $T$ satisfying
--
--   $$
--   r=1\iff \tau<M_n\ \lor\ \exists i<n,\ H(i),
--   \qquad T\le30+\sum_{i<n}(t_i+300).
--   $$
--
--   Its counter equals the mass of the first accepted prefix, or $M_n$ on failure; it retains the invariant and the same memory-preservation guarantee. This composes the fixed dispatcher into an ascending scan with immediate successful return.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingWantedScan.lean#L74-L138

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle17
import Definitions.Def_ThreeSum1962Source_Bundle18
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
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
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
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
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightReportingWantedDispatch
end ThreeSum.LightReportingWantedDispatch
namespace ThreeSum.SharedTraversalCosts
end ThreeSum.SharedTraversalCosts

theorem ThreeSum.LightReportingWantedScan.program_meets : ∀ {lim : Light.Limits} {μ : Nat → Int} {C : ThreeSum.LightReportingWantedDispatch.Config} {mass stepTime : Nat → Nat}
  {hit : Nat → Prop} {Inv : (Nat → Int) → Prop} {threshold n N D d : Nat}
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      lim.space)
  (hD :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) D
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      lim.depth)
  (hd : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d n) D)
  (hn : @LE.le.{0} Nat instLENat n N) (hInv : Inv μ)
  (hzero : @Eq.{1} Int (μ C.counter) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
  (hstep :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i N →
        ∀ (ν : Nat → Int) (e : Nat),
          @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) e i)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) D
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            Inv ν →
              @Eq.{1} Int (ν C.counter)
                  (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SharedTraversalCosts.prefixMass mass i)) →
                Light.Meets lim ThreeSum.LightReportingWantedDispatch.program
                  (@OfNat.ofNat.{0} Nat (nat_lit 151) (instOfNatNat (nat_lit 151))) e
                  (ThreeSum.LightReportingWantedDispatch.arguments C i) ν (stepTime i) fun (r : Int) (ξ : Nat → Int) =>
                  And
                    (Or (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                      (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                    (And
                      (Iff (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (Or
                          (@LT.lt.{0} Nat instLTNat threshold
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (ThreeSum.SharedTraversalCosts.prefixMass mass i) (mass i)))
                          (hit i)))
                      (And
                        (@Eq.{1} Int (ξ C.counter)
                          (@Nat.cast.{0} Int instNatCastInt
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (ThreeSum.SharedTraversalCosts.prefixMass mass i) (mass i))))
                        (And (Inv ξ)
                          (Light.KeptBut ν ξ C.layoutHeader C.counter
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))),
  Light.Meets lim ThreeSum.LightReportingWantedScan.program
    (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))) d
    (ThreeSum.LightReportingWantedDispatch.arguments C n) μ (ThreeSum.LightReportingWantedScan.time stepTime n)
    fun (r : Int) (ν : Nat → Int) =>
    And
      (Or (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      (And
        (Iff (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (ThreeSum.LightReportingWantedScan.Accepted mass hit threshold n))
        (And (ThreeSum.LightReportingWantedScan.Counter mass hit threshold n C.counter r ν)
          (And (Inv ν)
            (Light.KeptBut μ ν C.layoutHeader C.counter
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) := by
  sorry
