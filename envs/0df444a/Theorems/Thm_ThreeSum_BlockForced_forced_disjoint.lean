-- Prove2me | Theorems.Thm_ThreeSum_BlockForced_forced_disjoint
-- name    : ThreeSum.BlockForced.forced_disjoint
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T06:37:10.588305+00:00
-- url     : https://prove2.me/theorems/c7152ff1-29f6-4139-95ef-d2f0b53f7cd3
-- title:
--   Disjointness of the forced-prefix decomposition
-- statement:
--   Let $J,L\in\mathbb N$, let $I\subseteq\{0,\ldots,J-1\}$, and let $Q_i,u_i\subseteq\{0,\ldots,L-1\}$. Define $P_L=\{(i,a):i\in I,\ a\in u_i\}$, $P_R=\{(i,a):i\in I,\ a\in Q_i\setminus u_i\}$, and $R=\{(i,a):i\notin I,\ a\in Q_i\}$. For every $X\subseteq R$,
--
--   $$
--   (P_L\cup X)\cap(P_R\cup(R\setminus X))=\varnothing.
--   $$
--
--   No containment assumption on the $u_i$ is required for this disjointness claim. Together with the corresponding coverage identity, it supports the exact left/right decomposition used in prefix reporting.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BlockForced.lean#L70-L84

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
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
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting

theorem ThreeSum.BlockForced.forced_disjoint : ∀ {J L : Nat} (I : Finset.{0} (Fin J)) (Q u : Fin J → Finset.{0} (Fin L))
  (x : Finset.{0} (ThreeSum.BlockRows.Coord J L))
  (hx :
    @LE.le.{0} (Finset.{0} (ThreeSum.BlockRows.Coord J L))
      (@Preorder.toLE.{0} (Finset.{0} (ThreeSum.BlockRows.Coord J L))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (ThreeSum.BlockRows.Coord J L))
          (@Finset.instPartialOrder.{0} (ThreeSum.BlockRows.Coord J L))))
      x (@ThreeSum.BlockForced.remaining J L I Q)),
  @Disjoint.{0} (Finset.{0} (ThreeSum.BlockRows.Coord J L))
    (@Finset.instPartialOrder.{0} (ThreeSum.BlockRows.Coord J L))
    (@Finset.instOrderBot.{0} (ThreeSum.BlockRows.Coord J L))
    (@Union.union.{0} (Finset.{0} (ThreeSum.BlockRows.Coord J L))
      (@Finset.instUnion.{0} (ThreeSum.BlockRows.Coord J L) fun (a b : ThreeSum.BlockRows.Coord J L) =>
        @Sigma.instDecidableEqSigma.{0, 0} (Fin J) (fun (_i : Fin J) => Fin L) (instDecidableEqFin J)
          (fun (a : Fin J) => instDecidableEqFin L) a b)
      (@ThreeSum.BlockForced.prefixLeft J L I u) x)
    (@Union.union.{0} (Finset.{0} (ThreeSum.BlockRows.Coord J L))
      (@Finset.instUnion.{0} (ThreeSum.BlockRows.Coord J L) fun (a b : ThreeSum.BlockRows.Coord J L) =>
        @Sigma.instDecidableEqSigma.{0, 0} (Fin J) (fun (_i : Fin J) => Fin L) (instDecidableEqFin J)
          (fun (a : Fin J) => instDecidableEqFin L) a b)
      (@ThreeSum.BlockForced.prefixRight J L I Q u)
      (@SDiff.sdiff.{0} (Finset.{0} (ThreeSum.BlockRows.Coord J L))
        (@Finset.instSDiff.{0} (ThreeSum.BlockRows.Coord J L) fun (a b : ThreeSum.BlockRows.Coord J L) =>
          @Sigma.instDecidableEqSigma.{0, 0} (Fin J) (fun (_i : Fin J) => Fin L) (instDecidableEqFin J)
            (fun (a : Fin J) => instDecidableEqFin L) a b)
        (@ThreeSum.BlockForced.remaining J L I Q) x)) := by
  sorry
