-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalActualSourceSamplerBounds
-- name    : QuantumParallelRepetition.unconditionalActualSourceSamplerBounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T20:27:26.074099+00:00
-- url     : https://prove2.me/theorems/f409e51a-2429-44c3-9446-8e85d66f317c
-- title:
--   Existence of a rational local sampler with Pinsker-controlled coupling and mismatch
-- statement:
--   Let $G$ be a finite game, $S$ a strategy for $G^{\otimes n}$, and $D$ a coordinate set with at least one remaining
--   coordinate and positive postselection mass; fix a base history flag and a slack $\gamma > 0$. Then there exist a
--   positive common denominator $Q$ and integer numerators $\nu_k(r) \ge 0$, indexed by local sampler indices $k$ and
--   history flags $r$, such that: (i) $\sum_r \nu_k(r) = Q$ for every $k$, so each $\nu_k/Q$ is a probability
--   distribution on flags; (ii) $\nu$ is support preserving, $\nu_k(r) > 0$ whenever the exact local conditional family
--   assigns positive weight to $(k,r)$; (iii) each marked set $\{(r,t) : t < \nu_k(r)\}$ is nonempty; and, for the
--   shared-flag construction built from this data, (iv) the total variation between the flagged question distribution
--   and Alice's induced coupling is at most $\mathrm{Pinsker}(G,n,S,D) + \gamma$, and (v) the probability that Alice's
--   and Bob's permutation-decoded histories disagree is at most $4\bigl(\mathrm{Pinsker}(G,n,S,D) + \gamma\bigr)$, where
--   $\mathrm{Pinsker} = \sqrt{\text{(classical information rate)}/2}$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L66369-L66419

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_24
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.Pinsker
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.unconditionalActualSourceSamplerBounds
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (gamma : ℝ) (gamma_positive : 0 < gamma) :
    ∃ (denominator : ℕ), 0 < denominator ∧
      ∃ numerator : ExactLocalSamplerIndex X Y D →
        ExactHistoryFlag X Y A B D → ℕ,
        (∀ index, (∑ history, numerator index history) = denominator) ∧
        (∀ index history,
          0 < exactLocalConditionalFamily D base
              (exactLocallySampleableLaw G n S D)
              index history →
            0 < numerator index history) ∧
        ∃ nonempty : ∀ index,
            (rationalMarked denominator (numerator index)).Nonempty,
          QuantumParallelRepetition.Pinsker.finiteTotalVariation
              (flaggedQuestionWeight G
                (exactSourceSharedFlagWeight D denominator))
              (exactSourceAliceFlagCoupling
                G n S D denominator numerator nonempty) ≤
            exactSourcePinskerRate G n S D + gamma ∧
          (∑ outcome :
            ExactSourceSharedFlag X Y A B D denominator ×
              (X × Y),
            flaggedQuestionWeight G
              (exactSourceSharedFlagWeight D denominator) outcome *
              if exactSourcePermutationMatched
                  D denominator numerator nonempty outcome
                then 0 else 1) ≤
            4 * (exactSourcePinskerRate G n S D + gamma) := by sorry
