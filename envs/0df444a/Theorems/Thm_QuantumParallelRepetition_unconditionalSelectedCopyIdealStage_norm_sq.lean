-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalSelectedCopyIdealStage_norm_sq
-- name    : QuantumParallelRepetition.unconditionalSelectedCopyIdealStage_norm_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T15:29:55.001039+00:00
-- url     : https://prove2.me/theorems/3ea4a339-b2dc-4e7f-a278-f27932b77e71
-- title:
--   Squared norm of the ideal selected-copy stage equals the diagonal Born success probability
-- statement:
--   Fix a local dimension $d > 0$, a grid size $N > 0$, a phase count $B > 0$, a harmonic count $m > 0$, a width $w > 0$, and two bipartite unit vectors $\xi, \zeta$ on $\mathbb{C}^d \otimes \mathbb{C}^d$. The *ideal selected-copy stage* is the coherent target state of the public-bucket construction at these parameters. Its squared norm is shown to equal the diagonal Born success probability
--   $$
--   \big\|\,\mathrm{stage}_{w}(\xi,\zeta)\,\big\|^2 \;=\; \Pr\big[\text{both parties accept}\big],
--   $$
--   the joint acceptance probability of the rational soft-threshold POVM for $\xi$ and its transpose acting on the shared threshold density of the grid. In particular the squared norm is independent of $\zeta$, of the number of phases $B$ and of the number of harmonics $m$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L59449-L59483

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_24
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem QuantumParallelRepetition.unconditionalSelectedCopyIdealStage_norm_sq
    {d N B m : ℕ} {w : ℝ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : 0 < w)
    (ξ ζ : BipartiteUnitVector d) :
    ‖unconditionalSelectedCopyIdealStage
        (N := N) (B := B) (m := m) w ξ ζ‖ ^ 2 =
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ := by sorry
