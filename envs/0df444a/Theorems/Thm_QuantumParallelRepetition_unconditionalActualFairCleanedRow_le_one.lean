-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairCleanedRow_le_one
-- name    : QuantumParallelRepetition.unconditionalActualFairCleanedRow_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T19:24:10.567198+00:00
-- url     : https://prove2.me/theorems/8b3d42c6-32da-4c7a-9c43-53f88cbe5de5
-- title:
--   The cleaned integrator row has total squared mass at most one
-- statement:
--   Fix scales $S$, phases $B > 0$, grid size $N > 0$, local dimension $d > 0$, embezzlement parameter
--   $m > 0$, widths $\mathrm{width} : \mathrm{Fin}\,S \to \mathbb{R}$ all strictly positive, a schedule
--   $\mathrm{schedule} : \mathrm{Fin}\,L \to \mathrm{Fin}\,S$, unit vectors $\xi, \zeta$ of a bipartite
--   system of local dimension $d$, a cutoff $Q$, and two families of unitaries $A, C : \mathrm{Fin}\,B
--   \to \mathrm{Option}\,\mathbb{N} \to U(N m)$ describing the players' operations.
--
--   Then the cleaned integrator vectors produced at the $L$ rounds are jointly subnormalised:
--
--   $$
--   \sum_{j \in \mathrm{Fin}\,L}
--     \bigl\| v_{j} \bigr\|^{2} \le 1,
--   \qquad
--    v_{j} = \mathrm{integratorActualC485CleanedVector}\,Q\,\mathrm{width}\,\mathrm{schedule}\,
--      \xi\,\zeta\,A\,C\,j .
--   $$
--
--   The rounds are disjoint events of one stopping experiment, so their squared masses add up to at
--   most the total probability $1$ rather than to $L$. This is the row bound that lets the cleaned
--   integrator be treated as a sub-unit vector when the rounds are combined.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L66075-L66099

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_25
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
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
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalActualFairCleanedRow_le_one
    {S B N d L m : Nat}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (Q : Nat)
    (A C : Fin B → Option Nat →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    (∑ j : Fin L,
      ‖integratorActualC485CleanedVector
        Q width schedule ξ ζ A C j‖ ^ 2) ≤ 1 := by sorry
