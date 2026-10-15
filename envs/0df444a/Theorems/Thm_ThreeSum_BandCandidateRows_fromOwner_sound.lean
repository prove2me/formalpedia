-- Prove2me | Theorems.Thm_ThreeSum_BandCandidateRows_fromOwner_sound
-- name    : ThreeSum.BandCandidateRows.fromOwner_sound
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:11:30.332363+00:00
-- url     : https://prove2.me/theorems/7640242a-1796-48fc-976b-ae55976f5ad1
-- title:
--   Every flagged owner record describes a relevant in-range band triple
-- statement:
--   Let $A,B,C$ be finite ordered families of nonempty, pairwise separated integer intervals. An owner specifies an in-range $BC$, $AB$, or $AC$ index pair. Construct its record by looking up the missing interval at $C_k^--B_j^+$, $A_i^-+B_j^-$, or $C_k^--A_i^-$, respectively, encoding a successful lookup with flag one. If the resulting record $r=(\mathrm{flag},a,b,c)$ has $\mathrm{flag}=1$, then
--
--   $$
--   \begin{gathered}
--   a<|A|,\qquad b<|B|,\qquad c<|C|,\\
--   A_a^-+B_b^-\le C_c^+,\qquad C_c^-\le A_a^++B_b^+.
--   \end{gathered}
--   $$
--
--   Equivalently, its indices are valid and its band triple is relevant. This ensures that accepted physical candidate records satisfy the interval condition used in later counting and reporting arguments.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BandCandidateRows.lean#L139-L171

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
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
import Mathlib.Data.Nat.Log
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
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum_BinarySearch_locate_sound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress

theorem ThreeSum.BandCandidateRows.fromOwner_sound : ∀ (A B C : ThreeSum.BandEnumeration.Family) (o : ThreeSum.BandEnumeration.Owner A B C)
  (hf :
    @Eq.{1} Nat (ThreeSum.BandCandidateRows.fromOwner A B C o).flag
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
  have r := ThreeSum.BandCandidateRows.fromOwner A B C o;
  And (@LT.lt.{0} Nat instLTNat r.a A.size)
    (And (@LT.lt.{0} Nat instLTNat r.b B.size)
      (And (@LT.lt.{0} Nat instLTNat r.c C.size)
        (@ThreeSum.Bands.Relevant.{0, 0, 0} Nat Nat Nat A.lower A.upper B.lower B.upper C.lower C.upper
          (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat Nat) r.a (@Prod.mk.{0, 0} Nat Nat r.b r.c))))) := by
  sorry
