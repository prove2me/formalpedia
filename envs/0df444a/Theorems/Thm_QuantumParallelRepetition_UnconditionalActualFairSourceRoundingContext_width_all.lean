-- Prove2me | Theorems.Thm_QuantumParallelRepetition_UnconditionalActualFairSourceRoundingContext_width_all
-- name    : QuantumParallelRepetition.UnconditionalActualFairSourceRoundingContext.width_all
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T20:49:32.117215+00:00
-- url     : https://prove2.me/theorems/e493b521-f44e-4f6b-bf89-ea1e21b4eb2a
-- title:
--   Every stage of a rounding context has positive width
-- statement:
--   For a rounding context $c$, the associated width function is the constant function on the single stage index with
--   value the stored width $w$. The statement is that this function is strictly positive at every index: for all
--   $s \in \{0\}$, $0 < \mathrm{width}(c)(s)$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L70174-L70178

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_27
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
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
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
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

theorem QuantumParallelRepetition.UnconditionalActualFairSourceRoundingContext.width_all
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) : ∀ s : Fin 1, 0 < width c s := by sorry
