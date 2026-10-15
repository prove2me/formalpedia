-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_mem_allProducts
-- name    : ThreeSum.BandRawA.mem_allProducts
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:11:06.291865+00:00
-- url     : https://prove2.me/theorems/959012ad-6937-4f77-b90d-49875c952384
-- title:
--   Owner products are exactly the triples allowed by each raw-A label
-- statement:
--   Let $n_A,n_B,n_C,g\in\mathbb N$ and let $R$ be a list of band records. Form the raw-A label list $I$ by concatenating, for each flagged record, its truncated A band, retaining that record's owner index. For a physical label position $i$, let $o(i)$ be its owner record. Write $B_r$ and $C_r$ for that record's original B- and C-band positions, using the intervals $[bg,\min(n_B,(b+1)g))$ and $[cg,\min(n_C,(c+1)g))$. Let $\mathcal P$ be the union, over record slots, of the corresponding physical A-label positions crossed with these B and C bands. For every natural triple $(i,j,k)$,
--
--   $$
--   (i,j,k)\in\mathcal P\iff i<|I|\ \land\ j\in B_{o(i)}\ \land\ k\in C_{o(i)}.
--   $$
--
--   This identifies the exact domain represented by the physical owner catalog.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandRawAProduct.lean#L96-L112

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
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
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
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
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_row


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition

theorem ThreeSum.BandRawA.mem_allProducts : ∀ {nA nB nC g : Nat} {rs : List.{0} ThreeSum.BandCandidateRows.Record} {t : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)},
  Iff
    (@Membership.mem.{0, 0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) (Finset.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)))
      (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)))
        (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))))
      (ThreeSum.BandRawA.allProducts nA nB nC g rs) t)
    (And
      (@LT.lt.{0} Nat instLTNat (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) t)
        (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items nA g rs)))
      (And
        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
          (ThreeSum.BandRawA.bandPositions nB g
            (ThreeSum.BandRawA.ownerRecord nA g rs (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) t)).b)
          (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat Nat) t)))
        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
          (ThreeSum.BandRawA.bandPositions nC g
            (ThreeSum.BandRawA.ownerRecord nA g rs (@Prod.fst.{0, 0} Nat (Prod.{0, 0} Nat Nat) t)).c)
          (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} Nat (Prod.{0, 0} Nat Nat) t))))) := by
  sorry
