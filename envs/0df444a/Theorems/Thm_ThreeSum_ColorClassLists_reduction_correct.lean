-- Prove2me | Theorems.Thm_ThreeSum_ColorClassLists_reduction_correct
-- name    : ThreeSum.ColorClassLists.reduction_correct
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:43:38.74821+00:00
-- url     : https://prove2.me/theorems/4935ce06-dc68-4d19-b238-975ef9db93c4
-- title:
--   Distinct-position 3SUM reduces to the constructed color-class lists
-- statement:
--   Let $x:\{0,\ldots,n-1\}\to\mathbb Z$ and let $W\in\mathbb N$ satisfy $n\le2^W$. A coloring parameter selects two of the $W$ index-bit positions and a map from their Boolean pair to three colors. For each parameter $p$, form lists $A_p,B_p$ from the values in colors zero and one, and $C_p$ from the negated values in color two. Then
--
--   $$\exists\text{ pairwise distinct }i,j,k:\ x_i+x_j+x_k=0\iff\exists p,\ a\in A_p,\ b\in B_p,\ c\in C_p:\ a+b=c.$$
--
--   The lists preserve repeated values. The equivalence concerns distinct original positions and works for any sufficient index width, which connects the machine's class filtering to the original 3SUM problem.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/ColorClassLists.lean#L98-L119

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_Coloring_two_coordinates_separate


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter

theorem ThreeSum.ColorClassLists.reduction_correct : ∀ {n W : Nat} (x : Fin n → Int)
  (hn :
    @LE.le.{0} Nat instLENat n
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) W)),
  Iff (@ThreeSum.Coloring.DistinctZeroSum n x)
    (∃ (p : ThreeSum.Coloring.Parameter W), @ThreeSum.ColorClassLists.witness n W p x) := by
  sorry
