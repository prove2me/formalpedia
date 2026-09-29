-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualC485NormalizedDiagonalWork_mass_sum_le_one
-- name    : QuantumParallelRepetition.unconditionalActualC485NormalizedDiagonalWork_mass_sum_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T18:59:28.934146+00:00
-- url     : https://prove2.me/theorems/a803b8e6-be99-4fc8-8428-114da851ce69
-- title:
--   The normalized diagonal work vectors carry total mass at most one
-- statement:
--   With the same data as above (positive widths $w_1,\dots,w_S$, a schedule $s$ on $L$ stages, bipartite unit vectors
--   $\xi,\zeta$ on $\mathbb{C}^d \otimes \mathbb{C}^d$, and positive parameters $B, N, d, m$), let $D_j$ denote the
--   stage-$j$ *normalized diagonal work* vector, i.e. the retained-work vector of the first $j$ stages carrying the
--   canonical phase tail, rescaled by $\|\tau_{w_{s(j)}}(\xi)\| / \sqrt{w_{s(j)}\,d}$. Then these $L$ vectors form a
--   sub-normalized family:
--   $$\sum_{j=0}^{L-1} \bigl\| D_j \bigr\|^2 \;\le\; 1 .$$
--   Equivalently, the stopping ledger "survive the first $j$ stages, then pass the width-$w_{s(j)}$ diagonal test at
--   stage $j$" describes disjoint events and so has total probability at most one.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L63601-L63638

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_25
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem QuantumParallelRepetition.unconditionalActualC485NormalizedDiagonalWork_mass_sum_le_one
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    (∑ j : Fin L,
      ‖integratorActualC485NormalizedDiagonalWork
          (S := S) (B := B) (N := N) (d := d) (L := L)
          width schedule ξ ζ j‖ ^ 2) ≤ 1 := by sorry
