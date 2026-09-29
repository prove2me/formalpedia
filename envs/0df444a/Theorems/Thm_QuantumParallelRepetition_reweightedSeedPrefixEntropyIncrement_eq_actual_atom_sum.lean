-- Prove2me | Theorems.Thm_QuantumParallelRepetition_reweightedSeedPrefixEntropyIncrement_eq_actual_atom_sum
-- name    : QuantumParallelRepetition.reweightedSeedPrefixEntropyIncrement_eq_actual_atom_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T04:04:30.695394+00:00
-- url     : https://prove2.me/theorems/4bdb6271-c241-4330-aa13-e3cdffc71f2f
-- title:
--   Prefix entropy increment as an average of conditional relative entropies over atoms
-- statement:
--   Let $\lambda$ be a finite event law on an auxiliary index set $K$, let $\Pi : K \times \Omega_{\mathrm{out}} \to \Omega \times V^{h}$ be a projection recording a context and an $h$-letter register, fix a default letter $v_0 \in V$ and a position $k < h$, and assume the postselection mass is positive. Write $\mathrm{Post}$ for the posterior on $K \times \Omega_{\mathrm{out}}$ obtained by conditioning the product of $\lambda$ with the strategy's outcome law on the event that all coordinates of $D$ are won; write $J$ and $\Pi_0$ for the associated joint and prior laws on flagged contexts (a context together with the conditioned answer flag and the register); and for a flagged context $c$ let $c^{<k}$ be its prefix mask, which keeps register positions below $k$ and sets the rest to $v_0$. Then the $k$-th prefix entropy increment — the relative entropy of the masked pushforwards at cut $k+1$ minus the one at cut $k$ — equals the atomwise average
--   $$\sum_{q \in K \times \Omega_{\mathrm{out}}} \mathrm{Post}(q)\; D\Big(J_k\big(\cdot \mid \Pi^{\flat}(q)^{<k}\big) \,\Big\|\, \Pi_{0,k}\big(\cdot \mid \Pi^{\flat}(q)^{<k}\big)\Big),$$
--   where $\Pi^{\flat}(q)$ is the flagged context of $q$, and $J_k, \Pi_{0,k}$ are the laws of the pair (masked context, $k$-th letter) under $J$ and $\Pi_0$, so that the relative entropies compare the conditional distributions of the $k$-th letter.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L53260-L53376

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
set_option maxHeartbeats 3200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.reweightedSeedPrefixEntropyIncrement_eq_actual_atom_sum
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ}
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (default : V) (k : Fin h) :
    reweightedSeedPrefixEntropyIncrement
        seedLaw G n S D projection default k =
      ∑ point : K × ExactOutcome X Y A B n,
        reweightedSeedPosterior seedLaw G n S D point *
          finiteRelativeEntropy
            (jointConditional
              (groupedMass (exactPrefixNextCode default k)
                (reweightedSeedPrefixJoint
                  seedLaw G n S D projection))
              (finitePrefixMask default k.castSucc
                (((projection point).1,
                  repeatedConditionedAnswerFlag
                    G n S D point.2),
                  (projection point).2)))
            (jointConditional
              (groupedMass (exactPrefixNextCode default k)
                (reweightedSeedPrefixPrior
                  seedLaw G n S D projection))
              (finitePrefixMask default k.castSucc
                (((projection point).1,
                  repeatedConditionedAnswerFlag
                    G n S D point.2),
                  (projection point).2))) := by sorry
