-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactLocallySampleableLaw_absolute_continuous_roundedJA
-- name    : QuantumParallelRepetition.exactLocallySampleableLaw_absolute_continuous_roundedJA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T11:58:21.418599+00:00
-- url     : https://prove2.me/theorems/d76ed615-154b-494e-b853-9caba5dabaa1
-- title:
--   The postselected source law is absolutely continuous with respect to the rounded Alice surrogate
-- statement:
--   Assume $|\bar D| > 0$ and that the postselection mass is positive, and fix a base history flag $r_0$, a positive denominator $m$, and numerators $N_k(r) \in \mathbb{N}$ that are *support preserving*: $N_k(r) > 0$ whenever the local conditional family built from the postselected source law with base $r_0$ assigns positive mass to $r$ at the index $k$. Then the rounded Alice surrogate dominates the source law: for every tuple $t = (i,x,y,r)$, if $J_A^{\mathrm{rd}}(t) = \mu(x,y)\,N_{(i,x)}(r)/(m|\bar D|)$ vanishes, then the postselected source law $P$ satisfies $P(t) = 0$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L51125-L51202

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_23
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactLocallySampleableLaw_absolute_continuous_roundedJA
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (preserves : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (history : ExactLocallySampleableTuple X Y A B D) :
    exactLocallySampleableJARounded
      G n D denominator numerator history = 0 →
        exactLocallySampleableLaw G n S D history = 0 := by sorry
