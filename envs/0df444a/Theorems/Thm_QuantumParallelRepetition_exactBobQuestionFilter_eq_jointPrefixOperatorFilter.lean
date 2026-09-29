-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactBobQuestionFilter_eq_jointPrefixOperatorFilter
-- name    : QuantumParallelRepetition.exactBobQuestionFilter_eq_jointPrefixOperatorFilter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T08:45:01.481947+00:00
-- url     : https://prove2.me/theorems/6304b196-71bc-447a-8109-64d1de72d2f3
-- title:
--   Bob's question filter is the joint prefix operator filter with his distinguished question pinned
-- statement:
--   With $S$ a strategy for $G^{n}$ and $b\in B^{D}$ a tuple of Bob answers on the conditioned coordinates, let $E^{B}_{b}(\mathbf y)$ be Bob's conditioned effect operator, the sum of the POVM elements of his measurement on the question tuple $\mathbf y$ over all answer tuples agreeing with $b$ on $D$. Bob's question filter is
--   $$B^{b}_{h}(y)=\frac{1}{m_B(h,y)}\sum_{q'}\mathbf 1\big[\,c(q')=h\ \text{and}\ y'_i=y\,\big]\,\pi_n(q')\,E^{B}_{b}(\mathbf y'),$$
--   and $\Lambda^{B}_{F_X,F_Y}(b;q)$ denotes the conditional expectation of $E^{B}_{b}$ given that the questions agree with $q$ on the $X$-coordinates in $F_X$ and the $Y$-coordinates in $F_Y$, normalised by $Z(F_X,F_Y;q)$. The theorem states that for every question pair $q=(\mathbf x,\mathbf y)$,
--   $$B^{b}_{c(q)}\big(y_i\big)\;=\;\Lambda^{B}_{M_A,\,M_B\cup\{i\}}(b;q),$$
--   the exact mirror of the Alice-side identity: Bob's filter at the revealed history and his own question at the marked coordinate is the joint prefix filter in which his question at that coordinate has been added to the pinned set.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L37380-L37450

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_22
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactBobQuestionFilter_eq_jointPrefixOperatorFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n)
    (answer : {j : Fin n // j ∈ D} → B) :
    exactBobQuestionFilter G n S D seed
        (exactRevealCode D seed q) answer
        (q.2 seed.coordinate.val) =
      exactJointPrefixBobOperatorFilter G n S D
        (exactFairAliceQuestionMask D seed)
        (insert seed.coordinate.val
          (exactFairBobQuestionMask D seed))
        answer q.1 q.2 := by sorry
