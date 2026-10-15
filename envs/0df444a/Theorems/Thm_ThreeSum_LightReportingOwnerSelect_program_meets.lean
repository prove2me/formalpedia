-- Prove2me | Theorems.Thm_ThreeSum_LightReportingOwnerSelect_program_meets
-- name    : ThreeSum.LightReportingOwnerSelect.program_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:40:58.348982+00:00
-- url     : https://prove2.me/theorems/8e59c653-6b88-4d66-97c8-447d6661ce2a
-- title:
--   Verified selection of an incidence’s value and owner bands
-- statement:
--   Let $n,g\in\mathbb N$, $R$ be band-owner records, and $f:\mathbb N\to\mathbb Z$ the source array. Suppose memory $\mu$ stores the physical incidence list's values, owner labels, and position labels, and stores the four-cell records at base $r$. Let $N$ be the incidence count and $i<N$. Assume the value and owner arrays of length $N$, record array of length $4|R|$, and four-cell destination at $z$ fit in space $S$. Assume $S\le W$, the selected value has absolute value at most $W$, and the selected record's B/C band indices are at most $S$. At any call depth, the selector finishes within $700$ steps with
--
--   $$
--   \mathrm{result}=z,\qquad\nu[z:z+4]=[f(\mathrm{position}_i),\mathrm{owner}_i,R_{\mathrm{owner}_i}.b,R_{\mathrm{owner}_i}.c].
--   $$
--
--   It preserves every cell outside the destination. This recovers the original value and independent band choices from a physical incidence index.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightReportingOwnerSelect.lean#L37-L76

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
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
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
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
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
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
import Theorems.Thm_Light_seg_cons
import Theorems.Thm_ThreeSum_BandRawA_Stored_read
import Theorems.Thm_ThreeSum_BandRawA_mem_row


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightReportingOwnerSelect.program_meets : ∀ {lim : Light.Limits} {μ f : Nat → Int} {n g vals owners positions records i dst d : Nat}
  {rs : List.{0} ThreeSum.BandCandidateRows.Record}
  (H : ThreeSum.BandRawA.Stored μ vals owners positions f (ThreeSum.BandRawA.items n g rs))
  (HR : Light.Seg μ records (ThreeSum.BandCandidateRows.cells rs))
  (hi : @LT.lt.{0} Nat instLTNat i (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hvals :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) vals
        (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))
      lim.space)
  (howners :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) owners
        (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs)))
      lim.space)
  (hrecords :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) records
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@List.length.{0} ThreeSum.BandCandidateRows.Record rs)))
      lim.space)
  (hout :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) dst
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      lim.space)
  (hvalue :
    @LE.le.{0} Int Int.instLEInt
      (@abs.{0} Int instLatticeInt Int.instAddGroup (f (ThreeSum.BandRawA.labelAt n g rs i).position)) lim.word)
  (hB : @LE.le.{0} Nat instLENat (ThreeSum.BandRawA.ownerRecord n g rs i).b lim.space)
  (hC : @LE.le.{0} Nat instLENat (ThreeSum.BandRawA.ownerRecord n g rs i).c lim.space),
  Light.Meets lim ThreeSum.LightReportingOwnerSelect.program
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt vals)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt owners)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt records)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt i)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst) (@List.nil.{0} Int))))))
    μ (@OfNat.ofNat.{0} Nat (nat_lit 700) (instOfNatNat (nat_lit 700))) fun (result : Int) (ν : Nat → Int) =>
    And (@Eq.{1} Int result (@Nat.cast.{0} Int instNatCastInt dst))
      (And (Light.Seg ν dst (ThreeSum.LightReportingOwnerSelect.row f n g rs i))
        (Light.SameOutside μ ν dst (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) := by
  sorry
