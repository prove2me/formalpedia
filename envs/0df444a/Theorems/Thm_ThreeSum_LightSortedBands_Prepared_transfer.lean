-- Prove2me | Theorems.Thm_ThreeSum_LightSortedBands_Prepared_transfer
-- name    : ThreeSum.LightSortedBands.Prepared.transfer
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:42:37.419265+00:00
-- url     : https://prove2.me/theorems/4ef71fa7-e0ff-4f02-b583-30da7b032c2a
-- title:
--   Prepared sorted bands depend only on their allocated regions
-- statement:
--   Let $O$ be an integer list, let $v,e,g\in\mathbb N$, and let $\mu,\mu'$ be integer memories. The predicate $\mathcal P_\mu(v,e,g;O)$ means that some strictly increasing list of the same values as $O$, of length at most $|O|$, is stored at $v$, with the prescribed length and band-count headers and lower/upper endpoints at $e$. Suppose the memories agree throughout
--   $[v,v+|O|)$ and $[e,e+2+2|O|)$. Then
--
--   $$
--   \mathcal P_\mu(v,e,g;O)\Longrightarrow
--   \mathcal P_{\mu'}(v,e,g;O).
--   $$
--
--   The band-size parameter $g$ is any natural number.
--
--   This specifies exactly which regions must be retained when later machine stages modify other parts of memory.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightSortedBands.lean#L180-L203

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition

theorem ThreeSum.LightSortedBands.Prepared.transfer : ∀ {μ μ' : Nat → Int} {values endpoints g : Nat} {original : List.{0} Int}
  (h : ThreeSum.LightSortedBands.Prepared μ values endpoints g original)
  (hk :
    ∀ (a : Nat),
      Or
          (And (@LE.le.{0} Nat instLENat values a)
            (@LT.lt.{0} Nat instLTNat a
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) values (@List.length.{0} Int original))))
          (And (@LE.le.{0} Nat instLENat endpoints a)
            (@LT.lt.{0} Nat instLTNat a
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) endpoints
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int original))))) →
        @Eq.{1} Int (μ' a) (μ a)),
  ThreeSum.LightSortedBands.Prepared μ' values endpoints g original := by
  sorry
