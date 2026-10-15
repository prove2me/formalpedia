-- Prove2me | Theorems.Thm_ThreeSum_LightModuloCounts_meets
-- name    : ThreeSum.LightModuloCounts.meets
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:37:24.426983+00:00
-- url     : https://prove2.me/theorems/4762d1b2-53e2-4d0e-ba03-fc0667d00378
-- title:
--   Count modular three-list solutions from the original signed arrays
-- statement:
--   Let integer arrays $A,B,C$ have lengths $n_A,n_B,n_C\le N$, be stored entirely below scratch base $f$, and have entry magnitudes at most $U$. Fix $p>0$, and put $q=2^{\lceil\log_2p\rceil}$. Assume the specified capacity, residue, histogram, Karatsuba, cyclic-convolution, and lookup routines, with
--   $$f+13q+N+\lfloor\log_2(U+1)\rfloor+2\le S\le W,\quad128q^3(N+1)^2+4U+4p+16+N^3\le W,\quad d+\lceil\log_2p\rceil+3\le D.$$
--   The routine returns the exact count
--   $$r=\#\{(i,j,k):i<n_A,\ j<n_B,\ k<n_C,\ p\mid C_k-B_j-A_i\}.$$
--   It preserves all memory below $f$. The finite time budget includes capacity computation, two residue histograms, cyclic convolution, source residues, and the final lookup sum, with $400$ additional steps.
--
--   This turns modular triple counting into verified arithmetic on the original signed values.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightModuloCounts.lean#L50-L200

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

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
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_Histograms_tripleMass_eq_histogram
import Theorems.Thm_ThreeSum_LightCapacity_meets
import Theorems.Thm_ThreeSum_LightCyclic_correlation_meets
import Theorems.Thm_ThreeSum_LightLookupSum_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_meets
import Theorems.Thm_ThreeSum_LightResidues_residues_ends


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
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

theorem ThreeSum.LightModuloCounts.meets : ∀ {lim : Light.Limits} {P : Light.Program}
  {d pMain pCapacity pHist pCyclic pResidues pEmod pHistogram pMultiply pHalf pLinear pFill pLookup : Nat}
  (hmain :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pMain)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightModuloCounts.body pCapacity pHist pCyclic pResidues pLookup)))
  (hcap :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pCapacity)
      (@Option.some.{0} Light.Stmt ThreeSum.LightCapacity.body))
  (hhist :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pHist)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightResidueHistogram.body pResidues pHistogram)))
  (hres :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pResidues)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightResidues.residuesBody pEmod)))
  (hem :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pEmod)
      (@Option.some.{0} Light.Stmt Light.emodBody))
  (hcount :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pHistogram)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightHistogram.histogramBody pFill)))
  (hcyclic :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pCyclic)
      (@Option.some.{0} Light.Stmt (ThreeSum.LightCyclic.body pMultiply pLinear)))
  (K : ThreeSum.LightKaratsuba.Procs P pMultiply pHalf pLinear pFill)
  (hlookup :
    @Eq.{1} (Option.{0} Light.Stmt)
      (@GetElem?.getElem?.{0, 0, 0} Light.Program Nat Light.Stmt
        (fun (as : List.{0} Light.Stmt) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Light.Stmt as))
        (@List.instGetElem?NatLtLength.{0} Light.Stmt) P pLookup)
      (@Option.some.{0} Light.Stmt ThreeSum.LightLookupSum.body))
  {μ : Nat → Int} {a b c nA nB nC p N free U : Nat}
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (ha : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a nA) free)
  (hb : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b nB) free)
  (hc : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c nC) free)
  (hnA : @LE.le.{0} Nat instLENat nA N) (hnB : @LE.le.{0} Nat instLENat nB N) (hnC : @LE.le.{0} Nat instLENat nC N)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightModuloCounts.space free p N U) lim.space)
  (hword :
    @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightModuloCounts.word p N U)) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
          (Nat.clog (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) p))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      lim.depth)
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
          (@Nat.cast.{0} Int instNatCastInt U)),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt a)
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt b)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt c)
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nA)
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nB)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt nC)
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt p)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt N)
                    (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free) (@List.nil.{0} Int))))))))))
    μ (ThreeSum.LightModuloCounts.time p nA nB nC U) fun (r : Int) (μ' : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt
          (ThreeSum.ModuloCounts.count p nA nB nC
            (fun (i : Nat) => μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a i))
            (fun (i : Nat) => μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b i)) fun (i : Nat) =>
            μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c i))))
      (Light.Kept μ μ' free) := by
  sorry
