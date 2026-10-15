-- Prove2me | Theorems.Thm_ThreeSum_LightEncodedColorSources_program_meets
-- name    : ThreeSum.LightEncodedColorSources.program_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T18:01:59.589886+00:00
-- url     : https://prove2.me/theorems/9d3fb6d3-8bd8-417a-b462-98e0056b8930
-- title:
--   Place finite source banks after the retained wanted data
-- statement:
--   Let normalized lists $B,C$ represent original integer lists bounded by $U$, with band size $g>0$. Fix $p>0$, positive shift-selection modulus $M$, local parameters $h,J$, and cutoff $c\le512hJ$. At base $f$, suppose memory already stores the exact cover keys and wanted-setup output for list $X$, whose selected offset is $\delta$. The normalized values and their two-field headers precede $f$.
--
--   Let $b$ be the exact next-free address after the wanted data. Assume the source-controls space and word budgets at $b$, $S\le W$, and $d+512hJ+17\le D$. The routine returns the source finish address and establishes
--   $$\operatorname{FiniteSources}(\nu,b,g,p,h,J,c,B,C,\delta),$$
--   while retaining the cover data, wanted output, and every memory cell below $b$. Its time is exponentiation of the local prime through $J$, source-controls execution, and $1000$ extra steps.
--
--   This places the concrete source payload after the previously constructed wanted pairs.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightEncodedColorSources.lean#L52-L159

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
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
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
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
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
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
import Theorems.Thm_ThreeSum_EncodedColorCoverData_source_controls
import Theorems.Thm_ThreeSum_LightNatPower_meets
import Theorems.Thm_ThreeSum_LightSourceFinitePrepared_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMetadata
end ThreeSum.LightLocalCoverMetadata
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.SourceFiniteInputs
end ThreeSum.SourceFiniteInputs
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys
namespace ThreeSumApsp
end ThreeSumApsp

theorem ThreeSum.LightEncodedColorSources.program_meets : ∀ {lim : Light.Limits} {d : Nat} {μ : Nat → Int} {free bv be cv ce g p M h J cut U : Nat}
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  {hg : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g}
  {originalB originalC B C xs : List.{0} Int}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C}
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
        (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17))))
      lim.depth)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hcut :
    @LE.le.{0} Nat instLENat cut
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
  (hbv :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bv (@List.length.{0} Int originalB)) free)
  (hcv :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cv (@List.length.{0} Int originalC)) free)
  (hbe :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) be
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      free)
  (hce :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) ce
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      free)
  (hspace :
    @LE.le.{0} Nat instLENat
      (ThreeSum.LightSourceControlsHost.space (@ThreeSum.LightEncodedColorSources.sourceBase free p M h J inst xs)
        (@List.length.{0} Int B) (@List.length.{0} Int C) g p h J cut U M)
      lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt
        (ThreeSum.LightSourceControlsHost.word (@List.length.{0} Int B) (@List.length.{0} Int C) g p h J cut U M))
      lim.word)
  (hB : ThreeSum.LightBandPreprocessing.Represents μ bv be g hg originalB B hsB)
  (hC : ThreeSum.LightBandPreprocessing.Represents μ cv ce g hg originalC C hsC)
  (hboundB :
    ∀ (z : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) originalB z →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup z)
          (@Nat.cast.{0} Int instNatCastInt U))
  (hboundC :
    ∀ (z : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) originalC z →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup z)
          (@Nat.cast.{0} Int instNatCastInt U))
  (hcover : ThreeSum.LightCoverKeyData.Stored μ free h J)
  (hwanted :
    ThreeSum.LightWantedSetup.Output μ (ThreeSum.LightGuardedWanted.wantedFree free h J (@List.length.{0} Int xs)) M
      (ThreeSum.LightGuardedWanted.left p xs) (ThreeSum.LightGuardedWanted.right h J)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@List.length.{0} Int xs))
      (ThreeSum.LightGuardedWanted.totalKeys h J)
      (@Nat.cast.{0} Int instNatCastInt
        (@ThreeSum.RawAKeyLists.selected M inst (@Nat.cast.{0} Int instNatCastInt p) xs h J))),
  Light.Meets lim ThreeSum.LightEncodedColorSources.program
    (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cut)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt bv)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt be)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cv)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt ce)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt g)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                      (@List.cons.{0} Int
                        (@Nat.cast.{0} Int instNatCastInt
                          (ThreeSum.LightGuardedWanted.wantedFree free h J (@List.length.{0} Int xs)))
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free) (@List.nil.{0} Int))))))))))))
    μ (ThreeSum.LightEncodedColorSources.time (@List.length.{0} Int B) (@List.length.{0} Int C) g p h J cut U M)
    fun (r : Int) (ν : Nat → Int) =>
    And
      (ThreeSum.SourceFiniteData.Stored ν (@ThreeSum.LightEncodedColorSources.sourceBase free p M h J inst xs) g p h J
        cut B C
        (@Nat.cast.{0} Int instNatCastInt
          (@ThreeSum.RawAKeyLists.selected M inst (@Nat.cast.{0} Int instNatCastInt p) xs h J))
        r)
      (And (ThreeSum.LightCoverKeyData.Stored ν free h J)
        (And
          (ThreeSum.LightWantedSetup.Output ν
            (ThreeSum.LightGuardedWanted.wantedFree free h J (@List.length.{0} Int xs)) M
            (ThreeSum.LightGuardedWanted.left p xs) (ThreeSum.LightGuardedWanted.right h J)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@List.length.{0} Int xs))
            (ThreeSum.LightGuardedWanted.totalKeys h J)
            (@Nat.cast.{0} Int instNatCastInt
              (@ThreeSum.RawAKeyLists.selected M inst (@Nat.cast.{0} Int instNatCastInt p) xs h J)))
          (Light.Kept μ ν (@ThreeSum.LightEncodedColorSources.sourceBase free p M h J inst xs)))) := by
  sorry
