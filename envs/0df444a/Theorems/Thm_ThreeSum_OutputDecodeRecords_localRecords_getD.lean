-- Prove2me | Theorems.Thm_ThreeSum_OutputDecodeRecords_localRecords_getD
-- name    : ThreeSum.OutputDecodeRecords.localRecords_getD
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:29:08.781201+00:00
-- url     : https://prove2.me/theorems/96661de4-8eb0-40f5-a5bc-62d5956e17d4
-- title:
--   Quotient and remainder decode a local output-record index
-- statement:
--   Fix $h\in\mathbb N$, let $M=\binom{512h}{2h}$ be the output-layer size, and let $S=\operatorname{scheduleSize}(h)$. Local records enumerate the Cartesian product of schedule occurrences $0,\ldots,S-1$ and the fixed list of $2h$-element output subsets. Write $Q_r$ for the subset at position $r$ in that layer list. For every $i<SM$,
--
--   $$
--   \operatorname{localRecords}(h)[i]
--   =\left(\left\lfloor\frac iM\right\rfloor,\ Q_{i\bmod M}\right).
--   $$
--
--   Here $M>0$ for every $h$, including $h=0$, so both decoded coordinates are valid.
--
--   This identifies the exact physical record order used by the output decoder, preserving occurrence identity independently of whether two records have equal integer keys.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/OutputDecodeRecords.lean#L29-L50

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists

theorem ThreeSum.OutputDecodeRecords.localRecords_getD : ∀ {h i : Nat} (hi : @LT.lt.{0} Nat instLTNat i (ThreeSum.OutputDecodeRecords.localCount h)),
  @Eq.{1} (ThreeSum.GlobalEncoding.OutputBlock h)
    (@List.getD.{0} (ThreeSum.GlobalEncoding.OutputBlock h) (ThreeSum.GlobalKeyEnumeration.localRecords h) i
      (ThreeSum.OutputDecodeRecords.blockDefault h))
    (@Prod.mk.{0, 0} (ThreeSum.GlobalEncoding.Occurrence h)
      (↥(ThreeSum.LayerCounts.vertices
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)))
      (@Fin.mk (ThreeSum.GlobalEncoding.scheduleSize h)
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) i (ThreeSum.OutputDecodeRecords.layerCount h))
        (@Iff.mpr
          (@LT.lt.{0} Nat instLTNat
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) i
              (ThreeSum.OutputDecodeRecords.layerCount h))
            (ThreeSum.GlobalEncoding.scheduleSize h))
          (@LT.lt.{0} Nat instLTNat i
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (ThreeSum.GlobalEncoding.scheduleSize h)
              (ThreeSum.OutputDecodeRecords.layerCount h)))
          (@Nat.div_lt_iff_lt_mul (ThreeSum.OutputDecodeRecords.layerCount h) i (ThreeSum.GlobalEncoding.scheduleSize h)
            (ThreeSum.OutputDecodeRecords.layerCount_pos h))
          hi))
      (ThreeSum.GlobalKeyEnumeration.layerRecord h
        (@Fin.mk
          ((@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h).choose
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h))
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) i
            (ThreeSum.OutputDecodeRecords.layerCount h))
          (@Nat.mod_lt i (ThreeSum.OutputDecodeRecords.layerCount h) (ThreeSum.OutputDecodeRecords.layerCount_pos h))))) := by
  sorry
