-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawA_Procs_meets
-- name    : ThreeSum.LightBandRawA.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:14:11.066284+00:00
-- url     : https://prove2.me/theorems/fd855345-6c3a-43aa-87a4-f192a353dc75
-- title:
--   Construct the flattened physical A-incidence catalog
-- statement:
--   Let $r$ be $N$ four-cell owner records and let $f_0,\ldots,f_{n-1}$ be stored source values. Fix $g>0$ and require every record with flag $1$ to name a valid $A$ band. Both input regions end by output base $z$. Reserve three arrays of capacity $gN$, assume $z+3gN$ fits in space, $n+g+N+20$ fits in a word, space fits in a word, and $d+2$ is below the depth limit. The installed catalog procedures return
--   $$
--   q=|\operatorname{items}(n,g,r)|
--   $$
--   and store its parallel value, owner-slot, and source-position arrays at $z,z+gN,z+2gN$. Memory below $z$ is preserved, with budget $N(\operatorname{stepTime}(g)+200)+100$.
--
--   The flattened indices retain separate owner incidences even when original values coincide.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBandRawA.lean#L60-L164

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
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Theorems.Thm_Light_Ends_for
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons
import Theorems.Thm_ThreeSum_BandRawA_Stored_keep_before_append
import Theorems.Thm_ThreeSum_BandRawA_row_stored
import Theorems.Thm_ThreeSum_LightBandRawAStep_meets


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

theorem ThreeSum.LightBandRawA.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {μ : Nat → Int} {records src n g vals : Nat}
  {rs : List.{0} ThreeSum.BandCandidateRows.Record} {f : Nat → Int} {pMain : Nat}
  (S : ThreeSum.LightBandRawA.Procs P pMain)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      lim.depth)
  (hg : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g)
  (hrecords :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) records
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@List.length.{0} ThreeSum.BandCandidateRows.Record rs)))
      vals)
  (hsrc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src n) vals)
  (hspace :
    @LE.le.{0} Nat instLENat
      (ThreeSum.LightBandRawA.space vals (@List.length.{0} ThreeSum.BandCandidateRows.Record rs) g) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (ThreeSum.LightBandRawA.word n g (@List.length.{0} ThreeSum.BandCandidateRows.Record rs)))
      lim.word)
  (hvalid :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i (@List.length.{0} ThreeSum.BandCandidateRows.Record rs) →
        @Eq.{1} Nat
            (@List.getD.{0} ThreeSum.BandCandidateRows.Record rs i
                (@Inhabited.default.{1} ThreeSum.BandCandidateRows.Record
                  ThreeSum.BandCandidateRows.instInhabitedRecord)).flag
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @LT.lt.{0} Nat instLTNat
            (@List.getD.{0} ThreeSum.BandCandidateRows.Record rs i
                (@Inhabited.default.{1} ThreeSum.BandCandidateRows.Record
                  ThreeSum.BandCandidateRows.instInhabitedRecord)).a
            (ThreeSum.BandPartition.size n g))
  (hrecordRead : Light.Seg μ records (ThreeSum.BandCandidateRows.cells rs))
  (hread :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j n →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) src j)) (f j)),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt records)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} ThreeSum.BandCandidateRows.Record rs))
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt src)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt n)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt g)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt vals) (@List.nil.{0} Int)))))))
    μ (ThreeSum.LightBandRawA.time (@List.length.{0} ThreeSum.BandCandidateRows.Record rs) g)
    fun (r : Int) (ν : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items n g rs))))
      (And
        (ThreeSum.BandRawA.Stored ν vals
          (ThreeSum.LightBandRawA.ownerBase vals (@List.length.{0} ThreeSum.BandCandidateRows.Record rs) g)
          (ThreeSum.LightBandRawA.positionBase vals (@List.length.{0} ThreeSum.BandCandidateRows.Record rs) g) f
          (ThreeSum.BandRawA.items n g rs))
        (Light.Kept μ ν vals)) := by
  sorry
