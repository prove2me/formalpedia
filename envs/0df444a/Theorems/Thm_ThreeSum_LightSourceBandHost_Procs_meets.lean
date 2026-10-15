-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBandHost_Procs_meets
-- name    : ThreeSum.LightSourceBandHost.Procs.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T17:46:13.601687+00:00
-- url     : https://prove2.me/theorems/e565d955-1a52-49a6-a5fd-924a183ece25
-- title:
--   Build original source buckets and all retained source banks
-- statement:
--   Let stored integer arrays $f_L,f_R$ have lengths $N_L,N_R$, magnitudes at most $U$, and headers containing these lengths and their band counts for $g>0$. Fix $p>0$, local parameters $h,J$, cutoff $c\le512hJ$, and a stored shift $|\delta|\le E$. The arrays, headers, shift cell, and exact cover inputs all lie before base $b$.
--
--   Assume the specified pair and bank procedures, the maximum of their space and word budgets, $S\le W$, and $d+512hJ+15\le D$. The routine returns the defined finish address and constructs
--   $$\text{exact original-band residue buckets at }b\quad\text{and retained source banks at the prescribed following header}.$$
--   The bank data include the shared occurrence rows and both source orientations for each common band. Time is the pair-construction budget plus bank construction plus $500$; memory below $b$ is unchanged.
--
--   This joins original-value bucket construction with the retained subset-source catalogs used by reporting.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSourceBandHost.lean#L60-L137

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
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
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
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
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
import Theorems.Thm_ThreeSum_BlockSourceCoverInput_Input_of_kept
import Theorems.Thm_ThreeSum_LightSourceBandBanks_Procs_meets
import Theorems.Thm_ThreeSum_LightSourceBandPair_Procs_meets
import Theorems.Thm_ThreeSum_SourceBandPairData_Stored_of_kept


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

theorem ThreeSum.LightSourceBandHost.Procs.meets : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain : Nat} (C : ThreeSum.LightSourceBandHost.Procs P pMain)
  {μ : Nat → Int} {srcL headL srcR headR shiftCell base NL NR g p h J cut U D maps candidates histL histR : Nat}
  {shift : Int} (fL fR : Nat → Int)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
        (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15))))
      lim.depth)
  (hg : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hcut :
    @LE.le.{0} Nat instLENat cut
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
  (hsrcL : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcL NL) base)
  (hsrcR : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcR NR) base)
  (hheadL :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) headL
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      base)
  (hheadR :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) headR
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      base)
  (hshiftCell : @LT.lt.{0} Nat instLTNat shiftCell base)
  (hmaps :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
          (ThreeSum.GlobalEncoding.scheduleSize h)))
      base)
  (hcandidates :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) candidates
        (ThreeSum.GlobalEncoding.scheduleSize h))
      base)
  (hleft :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histL
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.LightLocalCoverSchedule.rows h)
          (ThreeSum.LocalCoverBounds.localPrime h)))
      base)
  (hright :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) histR
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.LightLocalCoverSchedule.rows h)
          (ThreeSum.LocalCoverBounds.localPrime h)))
      base)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightSourceBandHost.space base NL NR g p h J cut U D) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt
      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceBandHost.word NL NR g p h J U D)) lim.word)
  (hshift :
    @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup shift)
      (@Nat.cast.{0} Int instNatCastInt D))
  (hlenL : @Eq.{1} Int (μ headL) (@Nat.cast.{0} Int instNatCastInt NL))
  (hlenR : @Eq.{1} Int (μ headR) (@Nat.cast.{0} Int instNatCastInt NR))
  (hcountL :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) headL
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BandPartition.size NL g)))
  (hcountR :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) headR
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BandPartition.size NR g)))
  (hshiftRead : @Eq.{1} Int (μ shiftCell) shift)
  (hreadL :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NL →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcL j)) (fL j))
  (hreadR :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NR →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcR j)) (fR j))
  (hvaluesL :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NL →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (fL j))
          (@Nat.cast.{0} Int instNatCastInt U))
  (hvaluesR :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NR →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (fR j))
          (@Nat.cast.{0} Int instNatCastInt U))
  (hcover : ThreeSum.BlockSourceCoverInput.Input μ h maps candidates histL histR),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
      (@List.cons.{0} Int
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@OfNat.ofNat.{0} Int (nat_lit 512) (@instOfNat (nat_lit 512))) (@Nat.cast.{0} Int instNatCastInt h))
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt h)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localPrime h))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localBucketCap h))
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cut)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BlockSourceEncoding.modulus h J))
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maps)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt candidates)
                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt histL)
                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt histR)
                          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcL)
                            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt headL)
                              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt srcR)
                                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt headR)
                                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt g)
                                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                                      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt shiftCell)
                                        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt base)
                                          (@List.cons.{0} Int
                                            (@Nat.cast.{0} Int instNatCastInt
                                              (ThreeSum.SubsetAddress.downsetCap
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) J
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))
                                                    h))
                                                cut))
                                            (@List.cons.{0} Int
                                              (@Nat.cast.{0} Int instNatCastInt
                                                (ThreeSum.LightBlockSourceCatalog.count h J))
                                              (@List.cons.{0} Int
                                                (@Nat.cast.{0} Int instNatCastInt
                                                  (ThreeSum.GlobalEncoding.scheduleSize h))
                                                (@List.cons.{0} Int
                                                  (@Nat.cast.{0} Int instNatCastInt
                                                    (ThreeSum.SourceBandBankLayout.span h J cut))
                                                  (@List.nil.{0} Int))))))))))))))))))))))))
    μ (ThreeSum.LightSourceBandHost.time NL NR g p h J cut U D) fun (r : Int) (ν : Nat → Int) =>
    And (@Eq.{1} Int r (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightSourceBandHost.finish base NL NR g h J cut)))
      (And (ThreeSum.SourceBandPairData.Stored ν fL fR base NL NR g p (ThreeSum.BlockSourceEncoding.modulus h J) shift)
        (And
          (ThreeSum.SourceBandBankData.Stored ν fL fR (ThreeSum.LightSourceBandHost.bankHeader base NL NR g h J) NL NR g
            h J cut (ThreeSum.LightSourceBandHost.occurrenceBase base NL NR g h J) (@Nat.cast.{0} Int instNatCastInt p)
            shift)
          (Light.Kept μ ν base))) := by
  sorry
