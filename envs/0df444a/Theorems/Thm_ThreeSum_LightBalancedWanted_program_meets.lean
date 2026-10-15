-- Prove2me | Theorems.Thm_ThreeSum_LightBalancedWanted_program_meets
-- name    : ThreeSum.LightBalancedWanted.program_meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:43:52.831376+00:00
-- url     : https://prove2.me/theorems/ed6fe7d0-0df9-4f8c-ba37-f9b1ba920693
-- title:
--   Select a balanced residue shift and enumerate its exact wanted pairs
-- statement:
--   Let $M>0$ and let stored integer arrays $L_i$ and $R_j$, of lengths $N_L,N_R$, satisfy $|L_i|,|R_j|\le U$. Their regions end before free address $f$. Assume the maximum of the offset-selection and pair-enumeration workspace budgets fits, the corresponding word budgets fit, space fits in a word, and depth $d+\operatorname{clog}_2M+N_L+6$ is available. The program computes the prescribed balanced shift $\sigma\in[0,M)$ and stores a duplicate-free list of physical index pairs
--   $$
--   \mathcal P=\{(i,j):i<N_L,\ j<N_R,\ M\mid L_i+\sigma-R_j\},\qquad
--   M|\mathcal P|\le N_LN_R.
--   $$
--   It returns $f$, stores the pair count, pair address, next address, and shift in a four-cell header, preserves memory below $f$, and meets the balanced-wanted time budget.
--
--   Equal array values retain their distinct physical incidences.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightBalancedWanted.lean#L45-L101

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
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
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
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum_Histograms_correlation_histograms
import Theorems.Thm_ThreeSum_LightMinimum_least_value_le
import Theorems.Thm_ThreeSum_LightOriginalOffset_Procs_meets
import Theorems.Thm_ThreeSum_LightWantedSetup_program_meets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys

theorem ThreeSum.LightBalancedWanted.program_meets : ∀ {lim : Light.Limits} {μ : Nat → Int} {a b NL NR M free U d : Nat}
  [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (left right : Nat → Int)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (ha : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a NL) free)
  (hb : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b NR) free)
  (hspace : @LE.le.{0} Nat instLENat (@ThreeSum.LightBalancedWanted.space free M inst left right NL NR U) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightBalancedWanted.word M NL NR U))
      lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (Nat.clog (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) M))
          NL)
        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
      lim.depth)
  (hleft :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i NL →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a i)) (left i))
  (hright :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NR →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b j)) (right j))
  (hvaluesL :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i NL →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (left i))
          (@Nat.cast.{0} Int instNatCastInt U))
  (hvaluesR :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NR →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (right j))
          (@Nat.cast.{0} Int instNatCastInt U)),
  Light.Meets lim ThreeSum.LightBalancedWanted.program (@OfNat.ofNat.{0} Nat (nat_lit 25) (instOfNatNat (nat_lit 25))) d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt NL)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt NR)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt M)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free) (@List.nil.{0} Int)))))))
    μ (@ThreeSum.LightBalancedWanted.time M inst left right NL NR U) fun (r : Int) (ν : Nat → Int) =>
    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt free))
      (And
        (ThreeSum.LightWantedSetup.Output ν free M left right NL NR
          (@Nat.cast.{0} Int instNatCastInt (@ThreeSum.LightOriginalOffset.selected M inst left right NL NR)))
        (And
          (@LE.le.{0} Nat instLENat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) M (ν free).toNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) NL NR))
          (Light.Kept μ ν free))) := by
  sorry
