-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactAliceQuestionFilter_eq_jointPrefixOperatorFilter
-- name    : QuantumParallelRepetition.exactAliceQuestionFilter_eq_jointPrefixOperatorFilter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T08:37:11.175916+00:00
-- url     : https://prove2.me/theorems/46c1237b-609e-4c9c-b529-0ed439472e06
-- title:
--   Alice's question filter is the joint prefix operator filter with her distinguished question pinned
-- statement:
--   Fix in addition a strategy $S$ for $G^{n}$ and a tuple $a\in A^{D}$ of Alice answers on the conditioned coordinates, and let $E^{A}_{a}(\mathbf x)$ be Alice's conditioned effect operator: the sum of the POVM elements of her measurement on the question tuple $\mathbf x$ over all answer tuples agreeing with $a$ on $D$. Alice's question filter is the normalised average
--   $$A^{a}_{h}(x)=\frac{1}{m_A(h,x)}\sum_{q'}\mathbf 1\big[\,c(q')=h\ \text{and}\ x'_i=x\,\big]\,\pi_n(q')\,E^{A}_{a}(\mathbf x'),$$
--   while for masks $F_X,F_Y$ the joint prefix Alice filter is
--   $$\Lambda^{A}_{F_X,F_Y}(a;q)=\frac{1}{Z(F_X,F_Y;q)}\sum_{q'}\mathbf 1\big[\,\mathbf x'|_{F_X}=\mathbf x|_{F_X},\ \mathbf y'|_{F_Y}=\mathbf y|_{F_Y}\,\big]\,\pi_n(q')\,E^{A}_{a}(\mathbf x').$$
--   The theorem states that for every question pair $q=(\mathbf x,\mathbf y)$,
--   $$A^{a}_{c(q)}\big(x_i\big)\;=\;\Lambda^{A}_{M_A\cup\{i\},\,M_B}(a;q),$$
--   so the operator Alice attaches to the revealed history together with her own question at the marked coordinate is precisely the conditional expectation of her effect operator given the questions on $M_A\cup\{i\}$ and $M_B$. It is the operator-valued upgrade of the corresponding identity for scalar question masses.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L37308-L37378

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

theorem QuantumParallelRepetition.exactAliceQuestionFilter_eq_jointPrefixOperatorFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n)
    (answer : {j : Fin n // j ∈ D} → A) :
    exactAliceQuestionFilter G n S D seed
        (exactRevealCode D seed q) answer
        (q.1 seed.coordinate.val) =
      exactJointPrefixAliceOperatorFilter G n S D
        (insert seed.coordinate.val
          (exactFairAliceQuestionMask D seed))
        (exactFairBobQuestionMask D seed)
        answer q.1 q.2 := by sorry
