-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceRoundingContext_cleanBound
-- name    : QuantumParallelRepetition.unconditionalActualFairSourceRoundingContext_cleanBound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T20:52:59.157627+00:00
-- url     : https://prove2.me/theorems/4bb12a4e-0dae-4375-9661-7b53663a8b97
-- title:
--   Clean-deviation bound for the fair-source rounding context
-- statement:
--   Fix a game $G$, a strategy $S$ for $G^{\otimes n}$, a coordinate set $D$, and parameters $\alpha,\gamma$, and let $c$ be a fair-source rounding context for these data. Write $\lambda := \big(\text{postselection log-cost} + \text{answer log-cost}\big)/\big|\{0,\dots,n-1\}\setminus D\big|$ for the *martingale rate* of $(G,n,S,D)$, put
--   $$\beta \;:=\; 64\sqrt{\lambda} \;+\; \alpha^{1/3},$$
--   and let $\kappa := 16(e-1)+4$ be the bucket prefactor constant. The context supplies, for each locally sampleable history $h$ (weighted by the sampling law $\mu(h)$) and each branch index $j\in\{1,\dots,L\}$, an *actual* (cleaned) branch vector and its *canonical* (grid-rounded) counterpart. The theorem asserts that the resulting clean deviation
--   $$\mathrm{dev}(c)\;=\;\sum_{h}\mu(h)\sum_{j}\big\|\mathrm{actual}(h,j)-\mathrm{canonical}(h,j)\big\|^{2}$$
--   obeys
--   $$\mathrm{dev}(c)\;\le\;\frac{34}{\sqrt{\beta}}\cdot\beta\;+\;4\big(\alpha^{1/12}\big)^{2}\;+\;\kappa\sqrt{\beta}.$$
--   Thus the cost of replacing the actual branch vectors by their discretised canonical versions is controlled by the martingale rate and by $\alpha$ alone, with no dependence on the game's alphabets.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L70434-L70498

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_28
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
open UnconditionalActualFairSourceRoundingContext
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalActualFairSourceRoundingContext_cleanBound
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    deviation c ≤
      (34 / Real.sqrt
          (64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ))) *
        (64 * Real.sqrt (martingaleRate G n S D) +
          alpha ^ (1 / 3 : ℝ)) +
        4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt (martingaleRate G n S D) +
                alpha ^ (1 / 3 : ℝ)) := by sorry
