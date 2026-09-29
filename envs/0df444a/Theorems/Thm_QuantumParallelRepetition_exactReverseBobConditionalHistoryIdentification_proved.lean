-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseBobConditionalHistoryIdentification_proved
-- name    : QuantumParallelRepetition.exactReverseBobConditionalHistoryIdentification_proved
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T17:57:04.493099+00:00
-- url     : https://prove2.me/theorems/a85337f6-d020-4ee3-bcf4-072f3761831c
-- title:
--   Bob's conditional information equals the averaged reverse prefix information
-- statement:
--   In the same setting, with positive postselected mass, at least one free coordinate, an arbitrary base history flag and an arbitrary default letter, the two information quantities of the argument agree:
--   $$
--   I_{\mathrm{Bob}}(\text{base}) \;=\; I_{\mathrm{revprefix}} .
--   $$
--   On the left is the average, over Bob's side information (a free coordinate $i$ together with its question $y_i$), of the relative entropy between the true posterior conditional and the reference conditional built from Bob's locally sampleable law at the base flag. On the right is the average, over a random two-sided partition of the free coordinates, of the mean prefix entropy increment along the marked side. A notable consequence is that the left-hand side does not in fact depend on the base flag.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L57326-L57354

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_24
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactReverseBobConditionalHistoryIdentification_proved
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (default : X) :
    ExactReverseBobConditionalHistoryIdentification
      G n S D remaining base default := by sorry
