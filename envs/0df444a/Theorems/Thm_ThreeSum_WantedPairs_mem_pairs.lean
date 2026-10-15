-- Prove2me | Theorems.Thm_ThreeSum_WantedPairs_mem_pairs
-- name    : ThreeSum.WantedPairs.mem_pairs
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:23:46.108027+00:00
-- url     : https://prove2.me/theorems/a90b9055-c0df-4593-a22c-0d6901ed5849
-- title:
--   The stored bucket join contains exactly the equal-key index pairs
-- statement:
--   Let $N_L,N_R,M,o,f,i,j$ be natural numbers and let $\ell,\rho:\mathbb N\to\mathbb N$ be key functions satisfying $\ell(a)<M$ for $a<N_L$ and $\rho(b)<M$ for $b<N_R$. Suppose memory $\mu$ stores the stable buckets of the $N_R$ right indices, using offset base $o$ and flat-array base $f$. Form the pair list $P$ by visiting each $a<N_L$ and appending $(a,b)$ for every right index stored in the bucket of key $\ell(a)$. Then
--   $$(i,j)\in P\quad\Longleftrightarrow\quad i<N_L\ \land\ j<N_R\ \land\ \rho(j)=\ell(i).$$
--
--   This identifies the physical wanted-pair list with the exact equal-key join of the two original index ranges.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/WantedPairs.lean#L66-L84

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
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
import Theorems.Thm_ThreeSum_SourceBuckets_Stored_mem_bucketList


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets

theorem ThreeSum.WantedPairs.mem_pairs : ∀ {μ : Nat → Int} {offsets flat NR NL M i j : Nat} {left right : Nat → Nat}
  (H : ThreeSum.SourceBuckets.Stored μ right NR M offsets flat)
  (hl : ∀ (a : Nat), @LT.lt.{0} Nat instLTNat a NL → @LT.lt.{0} Nat instLTNat (left a) M)
  (hr : ∀ (b : Nat), @LT.lt.{0} Nat instLTNat b NR → @LT.lt.{0} Nat instLTNat (right b) M),
  Iff
    (@Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (List.{0} (Prod.{0, 0} Nat Nat))
      (@List.instMembership.{0} (Prod.{0, 0} Nat Nat)) (ThreeSum.WantedPairs.pairs μ offsets flat left NL)
      (@Prod.mk.{0, 0} Nat Nat i j))
    (And (@LT.lt.{0} Nat instLTNat i NL) (And (@LT.lt.{0} Nat instLTNat j NR) (@Eq.{1} Nat (right j) (left i)))) := by
  sorry
