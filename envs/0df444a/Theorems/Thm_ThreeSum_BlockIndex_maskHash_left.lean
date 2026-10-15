-- Prove2me | Theorems.Thm_ThreeSum_BlockIndex_maskHash_left
-- name    : ThreeSum.BlockIndex.maskHash_left
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:42:04.397565+00:00
-- url     : https://prove2.me/theorems/b39f2df2-3dd7-4321-8345-1317a366884f
-- title:
--   The flat mask evaluator equals the left endpoint hash
-- statement:
--   Let $h,J\in\mathbb N$, let $o$ select a local map occurrence in each block, and let $S$ be any subset of the $J$ blocks of $512h$ coordinates. Put $p=\operatorname{localPrime}(h)$ and let $a_{i,x,b}$ be the natural residue representative of the selected map at local coordinate $x$ and bit $b$. If $S_i$ is the row of $S$ in block $i$, then
--
--   $$
--   \operatorname{maskHash}(o,\mathrm{false},S)
--   =\sum_{i<J}p^i\sum_{x<512h}a_{i,x,\mathbf1_{x\in S_i}}
--   =\operatorname{endpointLeft}(o,S).
--   $$
--
--   The natural evaluator result is embedded in the integers. This connects flattened weighted-mask evaluation to the blockwise positional endpoint hash, without requiring the subset to be admissible.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockIndex.lean#L101-L118

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
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
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_OneHotMask_eval_maskOf


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

theorem ThreeSum.BlockIndex.maskHash_left : ∀ {h J : Nat} (o : ThreeSum.BlockEncoding.Occurrences h J)
  (S :
    Finset.{0}
      (ThreeSum.BlockRows.Coord J
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))),
  @Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt (@ThreeSum.BlockIndex.maskHash h J o Bool.false S))
    (@ThreeSum.BlockEncoding.endpointLeft h J o S) := by
  sorry
