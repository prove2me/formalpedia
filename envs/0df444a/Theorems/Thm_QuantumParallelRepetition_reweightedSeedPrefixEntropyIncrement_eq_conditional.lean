-- Prove2me | Theorems.Thm_QuantumParallelRepetition_reweightedSeedPrefixEntropyIncrement_eq_conditional
-- name    : QuantumParallelRepetition.reweightedSeedPrefixEntropyIncrement_eq_conditional
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T03:48:43.245498+00:00
-- url     : https://prove2.me/theorems/a4f081f5-65a0-4035-8742-db69d6a97c1d
-- title:
--   Chain rule: each prefix entropy increment is an averaged conditional relative entropy
-- statement:
--   In the same setting, let $J$ and $R$ be the prefix joint law and the prefix reference law on $(\Omega_0\times Z)\times V^{h}$, let $\Lambda_k$ be their relative entropy after all symbols of index $\ge k$ are reset to a default value, and let $\Delta_k=\Lambda_{k+1}-\Lambda_k$. The theorem identifies each increment as an averaged conditional divergence: $$\Delta_k=\sum_{c}J_{<k}(c)\;D\big(J(\,\cdot\mid c)\,\big\|\,R(\,\cdot\mid c)\big),$$ where $c$ ranges over contexts consisting of the $\Omega_0\times Z$ component together with the first $k$ symbols, $J_{<k}$ is the law of that context under $J$, and $J(\cdot\mid c)$, $R(\cdot\mid c)$ are the conditional laws of the $k$-th symbol given the context, under $J$ and under $R$ respectively. Thus the growth of relative entropy along the prefix filtration is exactly the expected divergence of the next symbol.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L32374-L32452

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_21
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.reweightedSeedPrefixEntropyIncrement_eq_conditional
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (default : V) (k : Fin h) :
    reweightedSeedPrefixEntropyIncrement
        seedLaw G n S D projection default k =
      ∑ context :
        (Ω × ConditionedAnswerFlag A B D) × (Fin h → V),
        groupedMass
            (finitePrefixMask default k.castSucc)
            (reweightedSeedPrefixJoint
              seedLaw G n S D projection)
            context *
          finiteRelativeEntropy
            (jointConditional
              (groupedMass
                (exactPrefixNextCode default k)
                (reweightedSeedPrefixJoint
                  seedLaw G n S D projection))
              context)
            (jointConditional
              (groupedMass
                (exactPrefixNextCode default k)
                (reweightedSeedPrefixPrior
                  seedLaw G n S D projection))
              context) := by sorry
