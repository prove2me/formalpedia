-- Prove2me | Theorems.Thm_ThreeSum_OneHotMask_eval_maskOf
-- name    : ThreeSum.OneHotMask.eval_maskOf
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-14T06:37:30.360828+00:00
-- url     : https://prove2.me/theorems/6f22a0f5-3c2a-4d71-974a-f7e8b14ad37d
-- title:
--   Evaluating a subset bit mask
-- statement:
--   Let $L\in\mathbb N$, let $S\subseteq\{0,\ldots,L-1\}$, and let $w_0,w_1:\mathbb N\to\mathbb N$. Encode $S$ by $m(S)=\sum_{i\in S}2^i$. The recursive mask evaluator selects the coefficient $w_1(i)$ for a set bit and $w_0(i)$ for an unset bit. Its value is exactly
--
--   $$
--   \operatorname{eval}(w_0,w_1,L,m(S))=\sum_{i=0}^{L-1}\begin{cases}w_1(i)&i\in S,\\w_0(i)&i\notin S.\end{cases}
--   $$
--
--   This connects the executable integer-mask recursion with the finite subset weight used in the combinatorial specification.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/OneHotMask.lean#L50-L71

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

theorem ThreeSum.OneHotMask.eval_maskOf : ∀ {L : Nat} (s : Finset.{0} Nat)
  (hs :
    @LE.le.{0} (Finset.{0} Nat)
      (@Preorder.toLE.{0} (Finset.{0} Nat)
        (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
      s (Finset.range L))
  (w0 w1 : Nat → Nat),
  @Eq.{1} Nat (ThreeSum.OneHotMask.eval w0 w1 L (ThreeSum.SubsetAddress.maskOf s))
    (∑ i ∈ Finset.range L,
      @ite.{1} Nat
        (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) s i)
        (@Finset.decidableMem.{0} Nat instDecidableEqNat i s) (w1 i) (w0 i)) := by
  sorry
