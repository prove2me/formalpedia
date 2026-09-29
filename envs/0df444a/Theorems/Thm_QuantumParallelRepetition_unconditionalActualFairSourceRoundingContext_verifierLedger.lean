-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceRoundingContext_verifierLedger
-- name    : QuantumParallelRepetition.unconditionalActualFairSourceRoundingContext_verifierLedger
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T20:53:14.718278+00:00
-- url     : https://prove2.me/theorems/20eb465a-a26c-458c-8699-fe29994ae161
-- title:
--   A fair-source rounding context satisfies the source verifier ledger
-- statement:
--   Let $c$ be a fair-source rounding context for $(G,n,S,D,\alpha,\gamma)$. For each locally sampleable history $h$ and branch $j$, let $E_{h,j}$ be the context's *winning-effect* operator on the branch space — the bounded operator built from the verifier predicate of $G$ together with the default answers $a_0\in A$, $b_0\in B$ — and let $\mathrm{actual}(h,j)$ and $\mathrm{source}(h,j)$ be the actual and source branch vectors. Writing $\langle z,Wz\rangle_{\mathrm{re}} := \operatorname{Re}\langle z, Wz\rangle$, the theorem asserts the four clauses of the *verifier ledger*: (i) every $E_{h,j}$ is a contraction, $\|E_{h,j}\|\le 1$; (ii) for every $h$ in the support of the sampling law and every $j$,
--   $$\operatorname{Re}\big\langle \mathrm{source}(h,j),\,E_{h,j}\,\mathrm{source}(h,j)\big\rangle \;=\; \|\mathrm{source}(h,j)\|^{2}\cdot p_{\mathrm{win}}(h),$$
--   where $p_{\mathrm{win}}(h)$ is the conditional winning probability of the original repeated strategy given $h$ (accepted-coordinate mass divided by $\mu(h)$); and (iii)–(iv) for every $h$ the total Born value on the actual vectors satisfies
--   $$0\;\le\;\sum_{j}\operatorname{Re}\big\langle \mathrm{actual}(h,j),\,E_{h,j}\,\mathrm{actual}(h,j)\big\rangle\;\le\;1.$$
--   Clause (ii) is what ties the abstract vector bookkeeping back to the game: on the exact source vectors the verifier effect reproduces the true conditional win probability.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L70623-L70677

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_28
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
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
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
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
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalActualFairSourceRoundingContext_verifierLedger
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
    {D : Finset (Fin n)} {alpha gamma : ℝ}
    (c : UnconditionalActualFairSourceRoundingContext
      G n S D alpha gamma) :
    UnconditionalActualFairCachedSourceVerifierLedger
      G n S D c.operator c.actual c.source := by sorry
