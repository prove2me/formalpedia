-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_relevant_product_complete
-- name    : ThreeSum.BandRawA.relevant_product_complete
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:39:44.380556+00:00
-- url     : https://prove2.me/theorems/5eae0aa6-feac-4d1a-8009-ac8f2e945390
-- title:
--   Every relevant band product appears in its physical owner domain
-- statement:
--   Let $A,B,C$ be finite, ordered families of nonempty, pairwise separated integer intervals. Let $t=(i,j,\ell)$ satisfy $A_i^{\rm lo}+B_j^{\rm lo}\le C_\ell^{\rm hi}$ and $C_\ell^{\rm lo}\le A_i^{\rm hi}+B_j^{\rm hi}$. For natural lengths $n_A,n_B,n_C$ and band width $g$, choose positions $p_A,p_B,p_C$ in the corresponding half-open index bands $[ag,\min(n,(a+1)g))$. Let $r$ be the canonical owner-record list, $s$ the physical slot of the owner of $t$, and $I$ its flattened $A$-incidence list. Then
--   $$
--   \exists k<|I|:\quad \operatorname{label}(k)=(s,p_A),\qquad
--   (k,p_B,p_C)\in\operatorname{ownerProduct}(r,s).
--   $$
--   Here the owner product combines that owner's physical $A$ indices with its original $B/C$ positions. Thus every relevant coordinate triple is retained with its physical incidence identity.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandRawAProduct.lean#L152-L178

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Theorems.Thm_ThreeSum_BandEnumeration_Family_lookup_sound
import Theorems.Thm_ThreeSum_BandEnumeration_candidate_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_BinarySearch_locate_complete


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
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress

theorem ThreeSum.BandRawA.relevant_product_complete : ∀ {A B C : ThreeSum.BandEnumeration.Family} {nA nB nC g pA pB pC : Nat} (t : ThreeSum.BandEnumeration.Triple A B C)
  (ht : ThreeSum.BandEnumeration.relevant A B C t)
  (ha :
    And
      (@LE.le.{0} Nat instLENat
        (ThreeSum.BandPartition.start g (@Fin.val A.size (@Prod.fst.{0, 0} A.Index (Prod.{0, 0} B.Index C.Index) t)))
        pA)
      (@LT.lt.{0} Nat instLTNat pA
        (ThreeSum.BandPartition.stop nA g
          (@Fin.val A.size (@Prod.fst.{0, 0} A.Index (Prod.{0, 0} B.Index C.Index) t)))))
  (hb :
    And
      (@LE.le.{0} Nat instLENat
        (ThreeSum.BandPartition.start g
          (@Fin.val B.size
            (@Prod.fst.{0, 0} B.Index C.Index (@Prod.snd.{0, 0} A.Index (Prod.{0, 0} B.Index C.Index) t))))
        pB)
      (@LT.lt.{0} Nat instLTNat pB
        (ThreeSum.BandPartition.stop nB g
          (@Fin.val B.size
            (@Prod.fst.{0, 0} B.Index C.Index (@Prod.snd.{0, 0} A.Index (Prod.{0, 0} B.Index C.Index) t))))))
  (hc :
    And
      (@LE.le.{0} Nat instLENat
        (ThreeSum.BandPartition.start g
          (@Fin.val C.size
            (@Prod.snd.{0, 0} B.Index C.Index (@Prod.snd.{0, 0} A.Index (Prod.{0, 0} B.Index C.Index) t))))
        pC)
      (@LT.lt.{0} Nat instLTNat pC
        (ThreeSum.BandPartition.stop nC g
          (@Fin.val C.size
            (@Prod.snd.{0, 0} B.Index C.Index (@Prod.snd.{0, 0} A.Index (Prod.{0, 0} B.Index C.Index) t)))))),
  ∃ (k : Nat),
    And
      (@LT.lt.{0} Nat instLTNat k
        (@List.length.{0} ThreeSum.BandRawA.Label
          (ThreeSum.BandRawA.items nA g (ThreeSum.BandCandidateRows.records A B C))))
      (And
        (@Eq.{1} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.labelAt nA g (ThreeSum.BandCandidateRows.records A B C) k)
          { owner := ThreeSum.BandCandidateRows.slot A B C (ThreeSum.BandEnumeration.owner A B C t), position := pA })
        (@Membership.mem.{0, 0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))
          (Finset.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)))
          (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)))
            (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) (@Finset.instSetLike.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))))
          (ThreeSum.BandRawA.ownerProduct nA nB nC g (ThreeSum.BandCandidateRows.records A B C)
            (ThreeSum.BandCandidateRows.slot A B C (ThreeSum.BandEnumeration.owner A B C t)))
          (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat Nat) k (@Prod.mk.{0, 0} Nat Nat pB pC)))) := by
  sorry
