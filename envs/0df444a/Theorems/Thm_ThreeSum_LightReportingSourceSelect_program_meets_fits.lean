-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSourceSelect_program_meets_fits
-- name    : ThreeSum.LightReportingSourceSelect.program_meets_fits
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:26:23.21798+00:00
-- url     : https://prove2.me/theorems/78abd7ac-aa60-42e6-85b3-aa1e813b0f66
-- title:
--   Verified selection of the fifteen reporting-source controls
-- statement:
--   Let $\mu$ be integer memory, and fix natural addresses for the pair, bank, and cover headers, the original $B,C$ arrays, and a destination $z$. Fix band indices $i,j$, occurrence code $c$, block count $J$, call depth $d$, and a pointer record $X$. Assume the header reads agree with $X$ and the exact individual fitting conditions hold within space bound $S$: the pair, bank, and cover headers of lengths $3,5,16$, both six-cell band headers, both selected stage cells, the fifteen output cells, the occurrence address, every output value, and $J+X.\mathrm{bankSpan}+20$ fit. Assume also $S\le W$, the word bound. The fixed selector terminates within $6000$ steps with
--
--   $$
--   \mathrm{result}=z,\qquad \nu(z+t)=\mathcal V_t\ (t<15),\qquad \nu(a)=\mu(a)\ (a\notin[z,z+15)).
--   $$
--
--   Here $\mathcal V$ contains the two source addresses, bucket offsets and flat arrays, band sizes, stage pointers, occurrence row, maps, candidates, and two histograms prescribed by $X$. This materializes the exact controls for wanted reporting.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingSourceSelect.lean#L67-L195

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
import Definitions.Def_ThreeSum1962Source_Bundle03
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
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection

theorem ThreeSum.LightReportingSourceSelect.program_meets_fits : ∀ {lim : Light.Limits} {μ : Nat → Int} {d pair bank cover srcB srcC i j code J dst : Nat}
  (X : ThreeSum.ReportingHostSourceSelection.Pointers)
  (H : ThreeSum.ReportingHostSourceSelection.HeaderReads μ X pair bank cover i j code)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hs : ThreeSum.ReportingHostSourceSelection.Fits X pair bank cover srcB srcC i j code J dst lim.space),
  Light.Meets lim ThreeSum.LightReportingSourceSelect.program
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt pair)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bank)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cover)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcB)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcC)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt i)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt j)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt code)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst) (@List.nil.{0} Int)))))))))))
    μ (@OfNat.ofNat.{0} Nat (nat_lit 6000) (instOfNatNat (nat_lit 6000))) fun (result : Int) (ν : Nat → Int) =>
    And (@Eq.{1} Int result (@Nat.cast.{0} Int instNatCastInt dst))
      (And (Light.SegN ν dst (ThreeSum.ReportingHostSourceSelection.values X srcB srcC code J))
        (Light.SameOutside μ ν dst (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))))) := by
  sorry
