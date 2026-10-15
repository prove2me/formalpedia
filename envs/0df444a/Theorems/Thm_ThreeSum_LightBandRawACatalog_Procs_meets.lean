-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawACatalog_Procs_meets
-- name    : ThreeSum.LightBandRawACatalog.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:28:51.145431+00:00
-- url     : https://prove2.me/theorems/10031be6-da14-446e-ad0a-7c5b5d117541
-- title:
--   Building the complete physical A-incidence catalog
-- statement:
--   Let $A,B,C$ be separated ordered interval families of sizes $a,b,c$, with their exact owner-lookup tables and two-cell length/count headers stored in memory. A source array $f$ has length $n$, and $A$ has $\lceil n/g\rceil$ bands for $g>0$. Put $N=bc+ab+ac$. The lookup tables, source array, and header pairs end before record base $r$; require
--   $$r+4N\le v,\quad v+3gN\le S\le W,\quad n+g+N+a+b+c+50\le W,\quad d+3<D.$$
--   For the specified candidate and raw-incidence procedures, the output includes all $N$ four-cell owner records in BC, AB, AC order. Enabled records contribute their A-band positions to an ordered incidence list $I$, and the parallel arrays satisfy
--   $$\nu(v+j)=f(I_j.\mathrm{position}),\quad\nu(v+gN+j)=I_j.\mathrm{owner},\quad\nu(v+2gN+j)=I_j.\mathrm{position}.$$
--   The return value is $|I|$; cells below $r$ are preserved. The budget is $N(59g+882)+106b+212a+668$.
--
--   This retains physical owners and original positions alongside every copied A value.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandRawACatalog.lean#L50-L125

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
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
import Mathlib.Data.List.Dedup
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
import Theorems.Thm_ThreeSum_BandCandidateRows_fromOwner_sound
import Theorems.Thm_ThreeSum_BandCandidateRows_mem_records_owner
import Theorems.Thm_ThreeSum_LightBandCandidates_Procs_meets
import Theorems.Thm_ThreeSum_LightBandRawA_Procs_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightBandRawACatalog.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {μ : Nat → Int}
  {tables rec src headerA headerB headerC nA nB nC g vals : Nat} {f : Nat → Int} {pMain : Nat}
  (S : ThreeSum.LightBandRawACatalog.Procs P pMain) (A B C : ThreeSum.BandEnumeration.Family)
  (hA : @Eq.{1} Nat A.size (ThreeSum.BandPartition.size nA g))
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      lim.depth)
  (hg : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g)
  (htable :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) tables
        (ThreeSum.LightBandEnumeration.count A.size B.size C.size))
      rec)
  (hsrc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src nA) rec)
  (hheadA :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) headerA
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      rec)
  (hheadB :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) headerB
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      rec)
  (hheadC :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) headerC
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      rec)
  (hrec :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) rec
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (ThreeSum.LightBandEnumeration.count A.size B.size C.size)))
      vals)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightBandRawACatalog.space vals A.size B.size C.size g) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBandRawACatalog.word nA A.size B.size C.size g)) lim.word)
  (hheaderA : ThreeSum.LightHeaderBands.At μ headerA nA A) (hheaderB : ThreeSum.LightHeaderBands.At μ headerB nB B)
  (hheaderC : ThreeSum.LightHeaderBands.At μ headerC nC C)
  (htables : ThreeSum.LightBandEnumeration.Tables μ tables A B C)
  (hread :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j nA →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src j)) (f j)),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt tables)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt rec)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt headerA)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt headerB)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt headerC)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt g)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt vals) (@List.nil.{0} Int)))))))))
    μ (ThreeSum.LightBandRawACatalog.time A.size B.size C.size g) fun (r : Int) (ν : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt
          (@List.length.{0} ThreeSum.BandRawA.Label
            (ThreeSum.BandRawA.items nA g (ThreeSum.BandCandidateRows.records A B C)))))
      (And (Light.Seg ν rec (ThreeSum.BandCandidateRows.cells (ThreeSum.BandCandidateRows.records A B C)))
        (And
          (ThreeSum.BandRawA.Stored ν vals
            (ThreeSum.LightBandRawA.ownerBase vals (ThreeSum.LightBandEnumeration.count A.size B.size C.size) g)
            (ThreeSum.LightBandRawA.positionBase vals (ThreeSum.LightBandEnumeration.count A.size B.size C.size) g) f
            (ThreeSum.BandRawA.items nA g (ThreeSum.BandCandidateRows.records A B C)))
          (Light.Kept μ ν rec))) := by
  sorry
