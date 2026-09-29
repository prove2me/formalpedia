-- Prove2me | Theorems.Thm_QuantumParallelRepetition_UnconditionalActualFairSourceRoundingContext_width_positive
-- name    : QuantumParallelRepetition.UnconditionalActualFairSourceRoundingContext.width_positive
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T19:03:08.489843+00:00
-- url     : https://prove2.me/theorems/3282c164-31b9-48ac-b6a9-8c866fb3c442
-- title:
--   The stored width of a rounding context is positive
-- statement:
--   Every rounding context — the bundle recording, for a game $G$, a repetition $n$, a strategy $S$, a coordinate set
--   $D$ and accuracy parameters $\alpha, \gamma$, that the remaining coordinate set is nonempty, the postselection mass
--   is positive, the uniform remaining failure is below $(1-\omega^*(G))/2$, and that sampler and stopping-hazard data
--   have been chosen — carries a stored width $w$ satisfying $w \ge 1$. In particular $w > 0$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L70169-L70172

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_26
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
open UnconditionalActualFairSourceRoundingContext
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
variable {D : Finset (Fin n)} {alpha gamma : ℝ}

theorem QuantumParallelRepetition.UnconditionalActualFairSourceRoundingContext.width_positive
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : 0 < c.stopping.w := by sorry
