-- Prove2me | Theorems.Thm_ThreeSum_IndexedGreedy_argmax_range
-- name    : ThreeSum.IndexedGreedy.argmax_range
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:38:10.388537+00:00
-- url     : https://prove2.me/theorems/52becf05-286a-460e-a5d1-945005506e59
-- title:
--   The first maximum equals a minimum scan of negated scores
-- statement:
--   Let $f:\mathbb N\to\mathbb N$ and $n>0$. Let $\operatorname{least}(g,n)$ be the left-to-right minimum scan of $g:\mathbb N\to\mathbb Z$ over indices $0,\ldots,n-1$, retaining the earlier index when values tie. Then the list maximum operation satisfies
--
--   $$
--   \operatorname{argmax}_{[0,\ldots,n-1]} f=\operatorname{some}\!\left(\operatorname{least}(-f,n)\right).
--   $$
--
--   Here the natural scores are embedded in the integers before negation. The result matches the tie rule of the mathematical greedy choice with the executable array scan.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/IndexedGreedy.lean#L16-L29

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
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
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LightMinimum
end ThreeSum.LightMinimum

theorem ThreeSum.IndexedGreedy.argmax_range : ∀ (f : Nat → Nat) {n : Nat}
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n),
  @Eq.{1} (Option.{0} Nat) (@List.argmax.{0, 0} Nat Nat Nat.instPreorder Nat.decLt f (List.range n))
    (@Option.some.{0} Nat
      (ThreeSum.LightMinimum.least
        (fun (i : Nat) => @Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt (f i))) n)) := by
  sorry
