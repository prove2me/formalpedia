-- Prove2me | Theorems.Thm_ThreeSum_LightColorScanHost_Procs_meets
-- name    : ThreeSum.LightColorScanHost.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:06:20.831919+00:00
-- url     : https://prove2.me/theorems/ed3cf033-9c64-465c-9679-bc4475640a70
-- title:
--   A complete color-family scan decides distinct-index 3SUM
-- statement:
--   Let $x:\{0,\ldots,n-1\}\to\mathbb Z$, set $w=\lfloor\log_2 n\rfloor+1$, and let $q=81w^2$ be the size of the concrete two-bit coloring family. Assume the specified scan procedures are present. Memory at the parameter address stores $\lfloor\log_2 n\rfloor$. For scratch base $f$, source address $s$, and parameter address $a$, require $s\le f$, $a<f$, $f+6\le S\le W$, $n+q+w+100\le W$, and $d+q+H+4\le D$.
--
--   Suppose each color backend, on every memory extension below $f$ and correctly stored six-field color parameter, finishes in $T$ steps using depth allowance $H$, returns its exact color-class witness test, and preserves memory below $f$. Then the host returns a Boolean $r$ satisfying
--   $$r=1\iff\exists i,j,k\text{ pairwise distinct},\quad x_i+x_j+x_k=0.$$
--   It preserves memory below $f$ and takes at most $q(100q+T+3000)+200$ steps.
--
--   This lifts the per-color decision contract to a complete 3SUM decision contract.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightColorScanHost.lean#L35-L71

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
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Finset.Image
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
import Mathlib.Data.Int.Basic
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
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_ColorClassLists_reduction_correct
import Theorems.Thm_ThreeSum_ColorParameters_index_lt
import Theorems.Thm_ThreeSum_LightColorScan_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.LightColorParametersCosts
end ThreeSum.LightColorParametersCosts
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds

theorem ThreeSum.LightColorScanHost.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {pMain src n params free colorTime colorDepth d : Nat}
  (R : ThreeSum.LightColorScanHost.Procs P pMain) (x : Fin n → Int) (μ : Nat → Int)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hspace :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free
        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
      lim.space)
  (hsrc : @LE.le.{0} Nat instLENat src free) (hparams : @LT.lt.{0} Nat instLTNat params free)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightColorScanHost.word n)) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (ThreeSum.ColorParameters.count (ThreeSum.LightColorParametersCosts.width n)))
          colorDepth)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      lim.depth)
  (hread : @Eq.{1} Int (μ params) (@Nat.cast.{0} Int instNatCastInt (ThreeSum.Scales.inputBits n)))
  (hcolor :
    ∀ (i : Nat)
      (hi : @LT.lt.{0} Nat instLTNat i (ThreeSum.ColorParameters.count (ThreeSum.LightColorParametersCosts.width n)))
      (ν : Nat → Int),
      Light.Kept μ ν free →
        Light.Seg ν free
            (@ThreeSum.ColorParameters.fields (ThreeSum.LightColorParametersCosts.width n)
              (@ThreeSum.ColorParameters.parameter (ThreeSum.LightColorParametersCosts.width n) i hi)) →
          ∀ (dd : Nat),
            @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dd colorDepth)
                lim.depth →
              Light.Meets lim P
                (@ThreeSum.LightColorScan.Procs.pColor P (@ThreeSum.LightColorScanHost.Procs.pScan P pMain R)
                  (@ThreeSum.LightColorScanHost.Procs.scan P pMain R))
                dd
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt params)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free)
                        (@List.cons.{0} Int
                          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
                            (@Nat.cast.{0} Int instNatCastInt free)
                            (@OfNat.ofNat.{0} Int (nat_lit 6) (@instOfNat (nat_lit 6))))
                          (@List.nil.{0} Int))))))
                ν colorTime fun (r : Int) (ξ : Nat → Int) =>
                And
                  (Or (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
                    (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                  (And
                    (Iff (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@ThreeSum.ColorClassLists.witness n (ThreeSum.LightColorParametersCosts.width n)
                        (@ThreeSum.ColorParameters.parameter (ThreeSum.LightColorParametersCosts.width n) i hi) x))
                    (Light.Kept ν ξ free))),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt params)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free) (@List.nil.{0} Int)))))
    μ (ThreeSum.LightColorScanHost.time colorTime n) fun (r : Int) (ξ : Nat → Int) =>
    And
      (Or (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      (And
        (Iff (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@ThreeSum.Coloring.DistinctZeroSum n x))
        (Light.Kept μ ξ free)) := by
  sorry
