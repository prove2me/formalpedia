-- Prove2me | Theorems.Thm_ThreeSum_LightGlobalKeys_Procs_meets_with_masks
-- name    : ThreeSum.LightGlobalKeys.Procs.meets_with_masks
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T16:28:24.06641+00:00
-- url     : https://prove2.me/theorems/edcc43d4-b57c-46a7-bed2-6024c7aab6cf
-- title:
--   Constructing global keys while retaining the output-mask layer
-- statement:
--   Fix $h,J$, put $L=512h$, $p=\operatorname{localPrime}(h)$, $q=\operatorname{scheduleSize}(h)$, $M=\binom L{2h}$, and $m=qM$. Memory stores the exact false/true coefficient rows of all $q$ schedule occurrences in $2L$-cell records ending before free address $f$. Set $w=f+M+m$ and $H=w+\sum_{i<J}(1+m^i)$.
--
--   Assume the specified layer, local-key, and radix-key procedures. Require the routine's defined space and word budgets to fit $S,W$, with $S\le W$ and $d+L+J+5\le D$. Within its defined budget $T_{\mathrm{global}}(h,J)$, the constructor returns $H$ and writes
--   $$\nu(H)=m^J,\qquad\nu[H+1:H+1+m^J]=\operatorname{globalKeys}(h,J).$$
--   It also retains at $f$ the ordered masks of every $2h$-subset of the local ground set and preserves every cell below $f$.
--
--   The global list retains all schedule and output occurrences, including equal keys.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightGlobalKeys.lean#L90-L183

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
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle11
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
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
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
import Mathlib.Data.Nat.Notation
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
import Theorems.Thm_ThreeSum_GlobalKeyEnumeration_rawOutput_abs_le
import Theorems.Thm_ThreeSum_LightLocalKeys_Procs_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_meets
import Theorems.Thm_ThreeSum_LocalKeyArraySemantics_seg_flatMap_rows
import Theorems.Thm_ThreeSum_OneHotMask_eval_maskOf


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.OneHotMask
end ThreeSum.OneHotMask
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

theorem ThreeSum.LightGlobalKeys.Procs.meets_with_masks : ∀ {lim : Light.Limits} {P : Light.Program} {d pMain h J maps free : Nat} {μ : Nat → Int}
  (S : ThreeSum.LightGlobalKeys.Procs P pMain)
  (hw : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt lim.space) lim.word)
  (hd :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
          J)
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
      lim.depth)
  (hspace : @LE.le.{0} Nat instLENat (ThreeSum.LightGlobalKeys.space free h J) lim.space)
  (hword : @LE.le.{0} Int Int.instLEInt (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LightGlobalKeys.word h J)) lim.word)
  (hmaps :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.GlobalEncoding.scheduleSize h)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
      free)
  (hreadFalse :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j (ThreeSum.GlobalEncoding.scheduleSize h) →
        ∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat i
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h) →
            @Eq.{1} Int
              (μ
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) j
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
                  i))
              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BlockCoefficientRows.mapRow h Bool.false j i)))
  (hreadTrue :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j (ThreeSum.GlobalEncoding.scheduleSize h) →
        ∀ (i : Nat),
          @LT.lt.{0} Nat instLTNat i
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h) →
            @Eq.{1} Int
              (μ
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) maps
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) j
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
                  i))
              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BlockCoefficientRows.mapRow h Bool.true j i))),
  Light.Meets lim P pMain d
    (@List.cons.{0} Int
      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
        (@OfNat.ofNat.{0} Int (nat_lit 512) (@instOfNat (nat_lit 512))) (@Nat.cast.{0} Int instNatCastInt h))
      (@List.cons.{0} Int
        (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) (@Nat.cast.{0} Int instNatCastInt h))
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.GlobalEncoding.scheduleSize h))
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localPrime h))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt J)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt maps)
                (@List.cons.{0} Int
                  (@Nat.cast.{0} Int instNatCastInt
                    (ThreeSum.LocalCoverBounds.outputCount
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                      h))
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt free) (@List.nil.{0} Int)))))))))
    μ (ThreeSum.LightGlobalKeys.time h J) fun (r : Int) (ν : Nat → Int) =>
    And
      (@Eq.{1} Int r
        (@Nat.cast.{0} Int instNatCastInt
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LightGlobalKeys.scratch free h)
            (ThreeSum.LightRadixKeys.offset (ThreeSum.LightGlobalKeys.localCount h) J))))
      (And
        (@Eq.{1} Int
          (ν
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LightGlobalKeys.scratch free h)
              (ThreeSum.LightRadixKeys.offset (ThreeSum.LightGlobalKeys.localCount h) J)))
          (@Nat.cast.{0} Int instNatCastInt
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (ThreeSum.LightGlobalKeys.localCount h) J)))
        (And
          (Light.Seg ν
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.LightGlobalKeys.scratch free h)
                (ThreeSum.LightRadixKeys.offset (ThreeSum.LightGlobalKeys.localCount h) J))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (ThreeSum.GlobalKeyEnumeration.globalKeys h J))
          (And
            (∀ (i : Nat),
              @LT.lt.{0} Nat instLTNat i
                  (ThreeSum.LocalCoverBounds.outputCount
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                    h) →
                @Eq.{1} Int (ν (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free i))
                  (@Nat.cast.{0} Int instNatCastInt
                    (ThreeSum.LocalMaskGraph.maskAt
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)
                      i)))
            (Light.Kept μ ν free)))) := by
  sorry
