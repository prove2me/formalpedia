-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceRoundingContext_stoppedVerifier
-- name    : QuantumParallelRepetition.unconditionalActualFairSourceRoundingContext_stoppedVerifier
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T01:43:52.608554+00:00
-- url     : https://prove2.me/theorems/326f29c2-4919-44f1-9973-225a6c9a3c21
-- title:
--   Win probability lower bound for the rounded strategy of a rounding context
-- statement:
--   Let $c$ be an `UnconditionalActualFairSourceRoundingContext` for a game $G$, a strategy $S$ on
--   $G^{n}$, a postselected set $D$, and parameters $\alpha, \gamma$. Then the rounded strategy's
--   winning probability satisfies
--
--   $$
--   1 - \frac{1 - \omega^{*}(G)}{2}
--     - 5\big(\mathrm{pinsker}(G,n,S,D) + \gamma\big)
--     - \Big(\big(64\sqrt{\mathrm{martingaleRate}(G,n,S,D)} + \alpha^{1/3} + \alpha^{2/3}\big)
--         + 4\sqrt{c.\mathrm{deviation}} + 2\sqrt{c.\mathrm{clipping}}\Big)
--   \;\le\; c.\mathrm{rounded}.\mathrm{winProbability}.
--   $$
--
--   This is the payoff of the whole rounding construction. Starting from a postselected strategy that
--   wins $G^{n}$ noticeably better than $\omega^{*}(G)$ would allow, it produces a single-copy
--   strategy whose winning probability is at least $1 - (1 - \omega^{*})/2$ minus a sum of error
--   terms, each of which the surrounding argument drives to zero: the Pinsker rate and slack
--   $\gamma$, the martingale rate, the rounding parameter $\alpha$ through $\alpha^{1/3}$ and
--   $\alpha^{2/3}$, and the context's own deviation and clipping energies under square roots.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L70735-L70777

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_28
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
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

theorem QuantumParallelRepetition.unconditionalActualFairSourceRoundingContext_stoppedVerifier
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    1 - (1 - entangledValue G) / 2 -
      5 * (exactSourcePinskerRate G n S D + gamma) -
        ((64 * Real.sqrt (martingaleRate G n S D) +
            alpha ^ (1 / 3 : ℝ) +
            (alpha ^ (1 / 3 : ℝ)) ^ 2) +
          4 * Real.sqrt c.deviation + 2 * Real.sqrt c.clipping) ≤
      c.rounded.winProbability := by sorry
