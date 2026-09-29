-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exact_source_equation_twenty_three_of_conditioned_reverse_prefix
-- name    : QuantumParallelRepetition.exact_source_equation_twenty_three_of_conditioned_reverse_prefix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T13:01:04.496144+00:00
-- url     : https://prove2.me/theorems/bd0eb1d9-bfa6-476e-b98d-b5ba8006ac4e
-- title:
--   Classical information rate bound for the postselected source law, from reverse-prefix identifications
-- statement:
--   Let $G$ be a finite two-player one-round game with question distribution $\mu$ and verifier predicate $V$, let $S$ be a strategy for the $n$-fold repetition $G^n$, and let $D \subseteq \{1,\dots,n\}$ be the set of already-conditioned coordinates, with at least one remaining coordinate ($|\bar D| > 0$, where $\bar D = \{1,\dots,n\} \setminus D$) and with positive postselection mass $p = \Pr[\,S \text{ wins every coordinate of } D\,] > 0$. Write $P$ for the law of the sampled tuple $(i, x_i, y_i, r)$ — a uniformly chosen remaining coordinate $i$, the two questions asked there, and the revealed history flag $r$ (seed, revealed questions, and both players' answers on $D$) — under the postselected joint distribution; and write $J_A^{r_0}, J_B^{r_0}$ for the two *locally sampleable* surrogates, in which $(x,y)$ is drawn from $\mu$ independently of $i$ and the history is drawn from Alice's, respectively Bob's, local conditional, defaulting to a fixed base flag $r_0$ off the support. Assume that Alice's and Bob's conditional source information terms admit the reverse-partition representation
--   $$\sum_{\Sigma \subseteq \bar D} w(\Sigma) \cdot \frac{1}{|\Sigma|} \sum_{k < |\Sigma|} \Delta_k(\Sigma),$$
--   an average, over sides $\Sigma$ weighted by the reverse partition weight $w$, of the mean per-position prefix entropy increments $\Delta_k$ of the corresponding reweighted-seed prefix laws (for auxiliary finite index types, seed laws, projections and default letters supplied as data). Then both surrogates satisfy the classical information rate bound
--   $$D\big(P \,\big\|\, J_A^{r_0}\big) \le \frac{3\log(1/p) + 2\,|D|\log(|A|\,|B|)}{|\bar D|}, \qquad D\big(P \,\big\|\, J_B^{r_0}\big) \le \frac{3\log(1/p) + 2\,|D|\log(|A|\,|B|)}{|\bar D|}.$$
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L47888-L47978

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_21
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.PartialOrder
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
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exact_source_equation_twenty_three_of_conditioned_reverse_prefix
    {KA KB : Type*} [Fintype KA] [Fintype KB]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (seedLawA : Finset (SourceRemainingCoordinate D) →
      FiniteEventLaw KA)
    (seedLawB : Finset (SourceRemainingCoordinate D) →
      FiniteEventLaw KB)
    (ΩA ΩB : Finset (SourceRemainingCoordinate D) → Type*)
    [∀ side, Fintype (ΩA side)]
    [∀ side, Fintype (ΩB side)]
    (projectionA : ∀ side : Finset (SourceRemainingCoordinate D),
      KA × ExactOutcome X Y A B n →
        ΩA side × (Fin side.card → Y))
    (projectionB : ∀ side : Finset (SourceRemainingCoordinate D),
      KB × ExactOutcome X Y A B n →
        ΩB side × (Fin side.card → X))
    (defaultY : Y) (defaultX : X)
    (aliceConditionedReverseIdentification :
      exactAliceSourceConditionalInformation G n S D base =
        ∑ side : Finset (SourceRemainingCoordinate D),
          reversePartitionWeight side *
            ((∑ k : Fin side.card,
              reweightedSeedPrefixEntropyIncrement
                (seedLawA side) G n S D
                (projectionA side) defaultY k) /
              (side.card : ℝ)))
    (bobConditionedReverseIdentification :
      exactBobSourceConditionalInformation G n S D base =
        ∑ side : Finset (SourceRemainingCoordinate D),
          reversePartitionWeight side *
            ((∑ k : Fin side.card,
              reweightedSeedPrefixEntropyIncrement
                (seedLawB side) G n S D
                (projectionB side) defaultX k) /
              (side.card : ℝ))) :
    ExactSourceClassicalInformationBound G n S D base := by sorry
