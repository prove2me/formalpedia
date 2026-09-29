-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalNormalizedCanonicalRetainedWork_norm_sq
-- name    : QuantumParallelRepetition.unconditionalNormalizedCanonicalRetainedWork_norm_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T16:28:27.61513+00:00
-- url     : https://prove2.me/theorems/0170c3fa-2803-4974-88b0-8cd1cfcb3f96
-- title:
--   Rescaled retained-work vector has the same mass as the ideal matched branch
-- statement:
--   Fix a grid resolution $N \ge 1$, a local dimension $d \ge 1$, a phase count $B \ge 1$ and a harmonic
--   parameter $m \ge 1$; fix strictly positive stage widths $w_1,\dots,w_S$, a stage schedule
--   $s : \{0,\dots,L-1\} \to \{1,\dots,S\}$, two bipartite unit vectors $\gamma,\varphi \in \mathbb{C}^d \otimes \mathbb{C}^d$,
--   a stage index $j$, and a unit vector $\rho$ on an auxiliary finite register. Write $w = w_{s(j)}$ and let
--   $\tau_w(\gamma)$ denote the canonical *accepted* (width-$w$, grid-$N$ clipped) target vector attached to $\gamma$.
--   Then rescaling the stage-$j$ retained-work vector $R_j$ — the tensor of the common-prefix failure vector of the
--   first $j$ stages with $\rho$ — by the scalar $\|\tau_w(\gamma)\| / \sqrt{w\,d}$ makes its mass agree exactly with
--   that of the stage-$j$ ideal matched branch vector $I_j$, which carries the full coherent target state on the
--   selected copy:
--   $$\left\| \frac{\|\tau_w(\gamma)\|}{\sqrt{w\,d}}\; R_j(\gamma,\varphi,\rho) \right\|^2 \;=\; \bigl\| I_j(\gamma,\varphi,\rho) \bigr\|^2 .$$
--   Both sides equal $\mathrm{Surv}_j(\gamma,\varphi)\cdot p_{\mathrm{diag}}(w,\gamma)$, the probability of surviving the
--   first $j$ stages times the diagonal Born success probability of the width-$w$ threshold test on $\gamma$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L63425-L63476

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_24
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
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
import Mathlib.Analysis.Normed.Group.Basic
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
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
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

theorem QuantumParallelRepetition.unconditionalNormalizedCanonicalRetainedWork_norm_sq
    {S N d L B m : ℕ} {T : Type*} [Fintype T]
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (gamma phi : BipartiteUnitVector d)
    (j : Fin L) (rest : EuclideanSpace ℂ T)
    (rest_unit : ‖rest‖ = 1) :
    ‖(‖dSVDensityRationalCanonicalAcceptedTarget
          (width (schedule j)) N gamma‖ /
        Real.sqrt ((width (schedule j)) * (d : ℝ))) •
      unconditionalSelectedCopyRetainedWork
        (N := N) width schedule gamma phi j rest‖ ^ 2 =
      ‖unconditionalSelectedCopyIdealMatchedBranch
        (N := N) (B := B) (m := m)
        width schedule gamma phi j rest‖ ^ 2 := by sorry
