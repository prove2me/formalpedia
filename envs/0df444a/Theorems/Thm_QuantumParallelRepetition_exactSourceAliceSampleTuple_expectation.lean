-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactSourceAliceSampleTuple_expectation
-- name    : QuantumParallelRepetition.exactSourceAliceSampleTuple_expectation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T11:43:04.952098+00:00
-- url     : https://prove2.me/theorems/3a580424-2b92-4700-8522-69eeff02baad
-- title:
--   Shared-permutation sampling realises the rounded Alice surrogate in expectation
-- statement:
--   Fix $D \subseteq \{1,\dots,n\}$, a denominator $m \in \mathbb{N}$, and nonnegative integers $N_k(r)$ indexed by local sampler indices $k$ and history flags $r$, subject to $\sum_r N_k(r) = m$ for every $k$ and to each marked set $\{(r,t) : t < N_k(r)\}$ being nonempty. Consider the sampling experiment in which a remaining coordinate $i \in \bar D$ and a permutation $\pi$ of $\mathcal{R} \times \{0,\dots,m-1\}$ ($\mathcal{R}$ the set of history flags) are drawn independently and uniformly, the question pair $(x,y)$ is drawn from $\mu$, and the sampled tuple is $\big(i, x, y, \mathrm{out}(\pi; N_{(i,x)})\big)$, where $\mathrm{out}(\pi;N)$ is the letter of the first marked point in the order induced by $\pi$. Then for every real-valued function $F$ on tuples,
--   $$\mathbb{E}\Big[F\big(i,x,y,\mathrm{out}(\pi;N_{(i,x)})\big)\Big] \;=\; \sum_{(i,x,y,r)} J_A^{\mathrm{rd}}(i,x,y,r)\, F(i,x,y,r), \qquad J_A^{\mathrm{rd}}(i,x,y,r) = \frac{\mu(x,y)\, N_{(i,x)}(r)/m}{|\bar D|}.$$
--   In other words, the shared-permutation sampler produces exactly the rounded Alice surrogate distribution $J_A^{\mathrm{rd}}$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L50625-L50733

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_23
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
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
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactSourceAliceSampleTuple_expectation
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ k, (∑ r, numerator k r) = denominator)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (value : ExactLocallySampleableTuple X Y A B D → ℝ) :
    (∑ outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y),
      flaggedQuestionWeight G
        (exactSourceSharedFlagWeight D denominator) outcome *
          value (exactSourceAliceSampleTuple
            D denominator numerator nonempty outcome)) =
      ∑ history : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableJARounded
          G n D denominator numerator history * value history := by sorry
